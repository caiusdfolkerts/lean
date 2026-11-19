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
/- Source: ProjectionCertificates/R_m15e10q1_1033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 285, 213, 357, 713, 329, 657, 406, 422, 282, 618, 298, 690, 740, 360, 21, 69, 261, 25, 73, 265, 521, 145, 529, 193, 321, 641, 390, 26, 42, 266, 522, 146, 274, 530, 162, 290, 546, 148, 276, 100, 164, 292, 196, 280, 104, 296, 328, 584, 656, 352, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_285, vertices_213, vertices_357, vertices_713, vertices_329, vertices_657, vertices_406, vertices_422, vertices_282, vertices_618, vertices_298, vertices_690, vertices_740, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_25, vertices_73, vertices_265, vertices_521, vertices_145, vertices_529, vertices_193, vertices_321, vertices_641, vertices_390, vertices_26, vertices_42, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_280, vertices_104, vertices_296, vertices_328, vertices_584, vertices_656, vertices_352, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_285), (false, vertices_213), (false, vertices_357), (false, vertices_713), (false, vertices_329), (false, vertices_657), (true, vertices_390), (true, vertices_42), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_164), (true, vertices_104), (true, vertices_296), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 15 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_390) then 16 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 329 1 657 42 266 146 274 162 290 546 164 104 296 608 672 539 390 285 213 357 713
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 390 406 2
cert_coverFacet 1 422
cert_cover_5 1 0 0 1 4 6 390 422 2
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 5 42 618 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 690
cert_cover_5 5 2 0 3 4 6 146 690 2
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1033

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_1034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 341, 709, 389, 425, 865, 94, 206, 58, 170, 818, 722, 316, 396, 848, 69, 133, 261, 161, 289, 545, 321, 577, 385, 641, 78, 26, 42, 138, 50, 82, 530, 162, 546, 194, 642, 28, 140, 268, 84, 276, 196, 388, 56, 168, 296, 392, 304, 336, 592, 784, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_341, vertices_709, vertices_389, vertices_425, vertices_865, vertices_94, vertices_206, vertices_58, vertices_170, vertices_818, vertices_722, vertices_316, vertices_396, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_78, vertices_26, vertices_42, vertices_138, vertices_50, vertices_82, vertices_530, vertices_162, vertices_546, vertices_194, vertices_642, vertices_28, vertices_140, vertices_268, vertices_84, vertices_276, vertices_196, vertices_388, vertices_56, vertices_168, vertices_296, vertices_392, vertices_304, vertices_336, vertices_592, vertices_784, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_341), (false, vertices_709), (false, vertices_389), (false, vertices_425), (false, vertices_865), (true, vertices_78), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_56), (true, vertices_304), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 389 26 42 138 50 82 530 194 28 140 268 56 304 592 784 675 78 341 709 425 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 82 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 3 4 7 8 818 50 3
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 206
cert_cover_5 1 1 0 1 2 6 78 206 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 818
cert_cover_5 4 2 0 3 4 7 50 818 3
cert_coverFacet 5 722
cert_cover_5 5 0 0 3 5 6 82 722 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 28 316 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1034

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_1035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 205, 421, 837, 217, 369, 654, 570, 154, 866, 418, 898, 604, 900, 624, 69, 133, 261, 201, 49, 81, 145, 161, 289, 321, 26, 138, 522, 50, 146, 162, 290, 546, 386, 642, 770, 76, 140, 524, 580, 388, 644, 772, 88, 152, 536, 112, 560, 592, 352, 608, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_205, vertices_421, vertices_837, vertices_217, vertices_369, vertices_654, vertices_570, vertices_154, vertices_866, vertices_418, vertices_898, vertices_604, vertices_900, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_201, vertices_49, vertices_81, vertices_145, vertices_161, vertices_289, vertices_321, vertices_26, vertices_138, vertices_522, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_580, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_536, vertices_112, vertices_560, vertices_592, vertices_352, vertices_608, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_205), (false, vertices_421), (false, vertices_837), (false, vertices_217), (false, vertices_369), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_644), (true, vertices_536), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_205) then 21 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 1 138 2 522 290 546 386 642 770 524 644 536 560 592 608 896 179 421 837 205 217 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 1 2 3 5 8 604 76 2
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 290 866 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 76 604 2
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1035

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_1036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 285, 333, 617, 817, 961, 30, 78, 182, 198, 554, 714, 930, 468, 432, 269, 25, 41, 73, 49, 273, 545, 321, 577, 769, 14, 22, 70, 134, 26, 42, 74, 522, 50, 162, 546, 194, 642, 28, 76, 148, 276, 196, 324, 552, 584, 176, 304, 400, 416, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_285, vertices_333, vertices_617, vertices_817, vertices_961, vertices_30, vertices_78, vertices_182, vertices_198, vertices_554, vertices_714, vertices_930, vertices_468, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_25, vertices_41, vertices_73, vertices_49, vertices_273, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_70, vertices_134, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_162, vertices_546, vertices_194, vertices_642, vertices_28, vertices_76, vertices_148, vertices_276, vertices_196, vertices_324, vertices_552, vertices_584, vertices_176, vertices_304, vertices_400, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_285), (false, vertices_333), (false, vertices_617), (false, vertices_817), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_134), (true, vertices_74), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_148), (true, vertices_196), (true, vertices_176), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 1 3 4 6 182 22 3
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 78
cert_cover_2 1 1 0 2 5 14 78 3
cert_coverFacet 2 182
cert_cover_5 2 2 0 1 3 4 22 182 3
cert_coverFacet 3 198
cert_cover_2 3 1 0 5 6 70 198 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 714
cert_cover_5 5 0 0 2 5 6 74 714 3
cert_coverFacet 6 930
cert_cover_5 6 1 0 4 6 7 162 930 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 148 468 2
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1036

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_1037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 331, 227, 781, 661, 233, 649, 626, 178, 338, 402, 852, 404, 696, 872, 67, 131, 259, 133, 261, 517, 73, 137, 265, 521, 225, 641, 50, 82, 146, 274, 98, 162, 322, 386, 148, 276, 532, 388, 772, 104, 168, 552, 328, 648, 776, 176, 560, 336, 592, 400, 656, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_331, vertices_227, vertices_781, vertices_661, vertices_233, vertices_649, vertices_626, vertices_178, vertices_338, vertices_402, vertices_852, vertices_404, vertices_696, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_225, vertices_641, vertices_50, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_322, vertices_386, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_104, vertices_168, vertices_552, vertices_328, vertices_648, vertices_776, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_656, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_331), (false, vertices_227), (false, vertices_781), (false, vertices_661), (false, vertices_233), (false, vertices_649), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_276), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 22 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_227) then 23 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 50 3
cert_row_4 1 1 3 5 7 8 852 276 2
cert_row_4 2 2 3 4 6 8 696 168 1
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 626
cert_cover_5 0 0 0 3 4 5 50 626 3
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 276 852 2
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 696
cert_cover_5 6 2 2 3 4 6 168 696 1
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1037

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_1038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 555, 835, 45, 181, 389, 929, 346, 538, 722, 60, 348, 212, 964, 696, 11, 259, 515, 13, 37, 133, 261, 41, 161, 545, 385, 769, 26, 266, 522, 82, 530, 322, 578, 28, 44, 268, 52, 84, 148, 196, 324, 388, 56, 344, 536, 552, 176, 208, 656, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_555, vertices_835, vertices_45, vertices_181, vertices_389, vertices_929, vertices_346, vertices_538, vertices_722, vertices_60, vertices_348, vertices_212, vertices_964, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_13, vertices_37, vertices_133, vertices_261, vertices_41, vertices_161, vertices_545, vertices_385, vertices_769, vertices_26, vertices_266, vertices_522, vertices_82, vertices_530, vertices_322, vertices_578, vertices_28, vertices_44, vertices_268, vertices_52, vertices_84, vertices_148, vertices_196, vertices_324, vertices_388, vertices_56, vertices_344, vertices_536, vertices_552, vertices_176, vertices_208, vertices_656, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_555), (false, vertices_835), (false, vertices_45), (false, vertices_181), (false, vertices_389), (false, vertices_929), (true, vertices_26), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_56), (true, vertices_344), (true, vertices_536), (true, vertices_208), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 15 else
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_344) then 21 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
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
cert_row_4 0 0 3 5 6 8 722 82 3
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_2 2 2 3 5 7 344
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 1 5 2
cert_heightProof 4
cert_coverFacet 0 346
cert_cover_5 0 2 0 2 3 5 26 346 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 722
cert_cover_5 2 0 0 3 5 6 82 722 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 348
cert_cover_5 4 2 1 2 3 5 28 348 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 964
cert_cover_5 6 1 1 5 6 7 196 964 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 56 696 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1038

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_1040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 77, 525, 341, 661, 433, 961, 558, 426, 458, 738, 316, 332, 564, 688, 13, 21, 69, 517, 73, 521, 145, 273, 321, 577, 385, 641, 42, 74, 394, 522, 162, 546, 194, 578, 44, 76, 268, 524, 52, 276, 532, 548, 324, 296, 328, 176, 304, 560, 656, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_77, vertices_525, vertices_341, vertices_661, vertices_433, vertices_961, vertices_558, vertices_426, vertices_458, vertices_738, vertices_316, vertices_332, vertices_564, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_517, vertices_73, vertices_521, vertices_145, vertices_273, vertices_321, vertices_577, vertices_385, vertices_641, vertices_42, vertices_74, vertices_394, vertices_522, vertices_162, vertices_546, vertices_194, vertices_578, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_548, vertices_324, vertices_296, vertices_328, vertices_176, vertices_304, vertices_560, vertices_656, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_77), (false, vertices_525), (false, vertices_341), (false, vertices_661), (false, vertices_433), (false, vertices_961), (true, vertices_42), (true, vertices_394), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_548), (true, vertices_296), (true, vertices_328), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_394) then 16 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 4 5 6 8 738 162 2
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 1 2 4 8 558 42 1
cert_row_4 3 1 2 3 4 7 316 44 2
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 42 558 1
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 42 426 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 738
cert_cover_5 3 0 0 4 5 6 162 738 2
cert_coverFacet 4 316
cert_cover_5 4 3 1 2 3 4 44 316 2
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1040

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_1041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 275, 531, 707, 565, 313, 617, 454, 434, 658, 812, 844, 180, 724, 420, 19, 67, 259, 515, 41, 73, 265, 49, 273, 529, 545, 577, 146, 274, 530, 194, 322, 386, 642, 780, 52, 148, 532, 164, 292, 548, 196, 324, 580, 388, 296, 552, 328, 584, 176, 304, 656, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_275, vertices_531, vertices_707, vertices_565, vertices_313, vertices_617, vertices_454, vertices_434, vertices_658, vertices_812, vertices_844, vertices_180, vertices_724, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_41, vertices_73, vertices_265, vertices_49, vertices_273, vertices_529, vertices_545, vertices_577, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_780, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_304, vertices_656, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_275), (false, vertices_531), (false, vertices_707), (false, vertices_565), (false, vertices_313), (false, vertices_617), (true, vertices_146), (true, vertices_386), (true, vertices_780), (true, vertices_148), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_176), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_531) then 1 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_780) then 19 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 3 4 6 7 434 146 2
cert_row_4 2 0 1 5 6 7 454 194 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 2 0 1 5 6 194 454 1
cert_coverFacet 1 434
cert_cover_5 1 1 0 3 4 6 146 434 2
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 812
cert_cover_5 3 0 1 2 4 7 780 812 2
cert_coverFacet 4 844
cert_cover_5 4 0 1 2 5 7 780 844 2
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1041

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_1042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 707, 387, 597, 229, 549, 425, 790, 410, 658, 348, 364, 804, 248, 720, 131, 259, 515, 37, 69, 517, 161, 289, 545, 193, 577, 385, 146, 274, 530, 386, 642, 770, 332, 84, 276, 532, 100, 292, 548, 772, 88, 152, 280, 104, 168, 296, 392, 208, 592, 656, 224, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_707, vertices_387, vertices_597, vertices_229, vertices_549, vertices_425, vertices_790, vertices_410, vertices_658, vertices_348, vertices_364, vertices_804, vertices_248, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_69, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_332, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_392, vertices_208, vertices_592, vertices_656, vertices_224, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_707), (false, vertices_387), (false, vertices_597), (false, vertices_229), (false, vertices_549), (false, vertices_425), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_332), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 20 17 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_332) then 19 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_2 1 1 2 5 7 332
cert_row_4 2 0 2 3 6 7 410 146 1
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 146 410 1
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 348
cert_cover_5 3 1 1 2 3 5 332 348 2
cert_coverFacet 4 364
cert_cover_5 4 1 1 2 4 5 332 364 2
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1042

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_1043.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1043

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 205, 837, 409, 617, 777, 662, 806, 314, 626, 402, 724, 120, 216, 808, 69, 133, 261, 73, 137, 265, 521, 577, 385, 769, 134, 262, 518, 50, 146, 274, 530, 290, 546, 386, 660, 196, 580, 772, 56, 88, 152, 280, 104, 296, 552, 200, 776, 112, 208, 592, 400, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_205, vertices_837, vertices_409, vertices_617, vertices_777, vertices_662, vertices_806, vertices_314, vertices_626, vertices_402, vertices_724, vertices_120, vertices_216, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_73, vertices_137, vertices_265, vertices_521, vertices_577, vertices_385, vertices_769, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_660, vertices_196, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_552, vertices_200, vertices_776, vertices_112, vertices_208, vertices_592, vertices_400, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_205), (false, vertices_837), (false, vertices_409), (false, vertices_617), (false, vertices_777), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_660), (true, vertices_56), (true, vertices_88), (true, vertices_296), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_660) then 20 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 6 8 660
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 0 2 3 4 7 314 50 1
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 134 662 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 262 806 2
cert_coverFacet 2 314
cert_cover_5 2 2 0 2 3 4 50 314 1
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 50 626 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 724
cert_cover_5 5 0 1 3 5 6 660 724 2
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1043

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_1044.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1044

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 341, 805, 709, 345, 617, 662, 154, 282, 170, 818, 738, 220, 788, 232, 69, 261, 517, 41, 73, 265, 337, 289, 545, 577, 26, 42, 138, 266, 146, 274, 530, 162, 290, 546, 642, 84, 148, 276, 532, 196, 644, 772, 88, 152, 280, 104, 168, 200, 784, 224, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_341, vertices_805, vertices_709, vertices_345, vertices_617, vertices_662, vertices_154, vertices_282, vertices_170, vertices_818, vertices_738, vertices_220, vertices_788, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_337, vertices_289, vertices_545, vertices_577, vertices_26, vertices_42, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_784, vertices_224, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_341), (false, vertices_805), (false, vertices_709), (false, vertices_345), (false, vertices_617), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_148), (true, vertices_532), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_341) then 23 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 2 3 5 6 220 84 1
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 818
cert_cover_5 4 0 0 3 4 7 274 818 2
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 84 220 1
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1044

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_1045.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1045

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 355, 173, 313, 217, 849, 214, 678, 838, 810, 156, 540, 556, 596, 792, 99, 25, 41, 137, 81, 273, 161, 289, 193, 321, 70, 134, 518, 162, 290, 546, 194, 322, 770, 28, 44, 140, 524, 84, 148, 532, 164, 548, 580, 152, 280, 536, 296, 552, 776, 208, 592, 784, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_355, vertices_173, vertices_313, vertices_217, vertices_849, vertices_214, vertices_678, vertices_838, vertices_810, vertices_156, vertices_540, vertices_556, vertices_596, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_99, vertices_25, vertices_41, vertices_137, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_321, vertices_70, vertices_134, vertices_518, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_164, vertices_548, vertices_580, vertices_152, vertices_280, vertices_536, vertices_296, vertices_552, vertices_776, vertices_208, vertices_592, vertices_784, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_355), (false, vertices_173), (false, vertices_313), (false, vertices_217), (false, vertices_849), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_546), (true, vertices_770), (true, vertices_28), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_536), (true, vertices_552), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_776) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 70 2
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 0 2 4 7 8 810 290 1
cert_rows
cert_pivot_2 3 6 1 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 70 214 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 134 678 2
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 70 838 3
cert_coverFacet 3 810
cert_cover_5 3 3 0 2 4 7 290 810 1
cert_coverFacet 4 156
cert_cover_2 4 2 1 3 6 28 156 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1045

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_1046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 519, 707, 301, 837, 241, 369, 46, 526, 314, 538, 690, 348, 588, 728, 7, 131, 515, 37, 261, 517, 113, 161, 289, 193, 321, 577, 14, 38, 518, 26, 42, 522, 50, 530, 162, 642, 44, 76, 268, 524, 324, 580, 88, 280, 536, 296, 584, 176, 304, 208, 336, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_519, vertices_707, vertices_301, vertices_837, vertices_241, vertices_369, vertices_46, vertices_526, vertices_314, vertices_538, vertices_690, vertices_348, vertices_588, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_515, vertices_37, vertices_261, vertices_517, vertices_113, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_14, vertices_38, vertices_518, vertices_26, vertices_42, vertices_522, vertices_50, vertices_530, vertices_162, vertices_642, vertices_44, vertices_76, vertices_268, vertices_524, vertices_324, vertices_580, vertices_88, vertices_280, vertices_536, vertices_296, vertices_584, vertices_176, vertices_304, vertices_208, vertices_336, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_519), (false, vertices_707), (false, vertices_301), (false, vertices_837), (false, vertices_241), (false, vertices_369), (true, vertices_14), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_76), (true, vertices_524), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_584), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 7 348 76 2
cert_row_4 1 0 2 3 4 7 314 26 3
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 314
cert_cover_5 2 1 0 2 3 4 26 314 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 50 690 3
cert_coverFacet 5 348
cert_cover_5 5 0 1 2 3 5 76 348 2
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1046

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_1047.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1047

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [27, 587, 403, 355, 541, 721, 449, 286, 302, 106, 556, 692, 404, 484, 744, 11, 19, 67, 259, 25, 521, 145, 529, 193, 321, 577, 385, 270, 26, 42, 74, 274, 98, 290, 28, 44, 524, 148, 276, 532, 164, 292, 548, 388, 104, 552, 584, 400, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_27, vertices_587, vertices_403, vertices_355, vertices_541, vertices_721, vertices_449, vertices_286, vertices_302, vertices_106, vertices_556, vertices_692, vertices_404, vertices_484, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_67, vertices_259, vertices_25, vertices_521, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_270, vertices_26, vertices_42, vertices_74, vertices_274, vertices_98, vertices_290, vertices_28, vertices_44, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_104, vertices_552, vertices_584, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_27), (false, vertices_587), (false, vertices_403), (false, vertices_355), (false, vertices_541), (false, vertices_721), (false, vertices_449), (true, vertices_270), (true, vertices_42), (true, vertices_44), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_104), (true, vertices_552), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_403) then 19 else
  if p.val = (false, vertices_355) then 20 else
  if p.val = (false, vertices_541) then 15 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_270) then 16 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 1 27 0 449 42 44 148 276 164 292 548 388 104 552 224 672 541 270 587 403 355 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 7 270
cert_row_4 1 1 3 4 6 8 692 148 2
cert_row_4 2 1 4 5 6 7 484 164 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 270 286 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 270 302 3
cert_coverFacet 2 106
cert_cover_2 2 2 0 4 5 42 106 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 148 692 2
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 484
cert_cover_5 6 2 1 4 5 6 164 484 2
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1047

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_1048.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1048

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 181, 389, 905, 817, 737, 566, 614, 326, 346, 538, 714, 460, 228, 792, 21, 133, 261, 49, 273, 161, 545, 385, 641, 769, 22, 550, 70, 262, 26, 74, 522, 274, 530, 322, 578, 52, 100, 164, 196, 324, 388, 280, 536, 200, 328, 392, 648, 776, 560, 784, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_181, vertices_389, vertices_905, vertices_817, vertices_737, vertices_566, vertices_614, vertices_326, vertices_346, vertices_538, vertices_714, vertices_460, vertices_228, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_49, vertices_273, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_22, vertices_550, vertices_70, vertices_262, vertices_26, vertices_74, vertices_522, vertices_274, vertices_530, vertices_322, vertices_578, vertices_52, vertices_100, vertices_164, vertices_196, vertices_324, vertices_388, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_560, vertices_784, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_181), (false, vertices_389), (false, vertices_905), (false, vertices_817), (false, vertices_737), (true, vertices_550), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_550) then 17 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 389 70 26 74 522 530 322 578 100 196 324 280 536 200 328 279 550 181 905 817 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 8 550
cert_row_4 1 0 2 3 5 7 346 26 3
cert_row_4 2 0 2 5 6 8 714 74 3
cert_row_4 3 1 2 5 6 7 460 196 1
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 614
cert_cover_5 1 0 0 1 4 5 550 614 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 346
cert_cover_5 3 1 0 2 3 5 26 346 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 714
cert_cover_5 5 2 0 2 5 6 74 714 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 196 460 1
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1048

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_1049.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1049

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 93, 581, 409, 361, 657, 961, 286, 302, 550, 690, 402, 482, 108, 740, 21, 69, 517, 25, 73, 265, 145, 529, 321, 577, 385, 641, 270, 22, 38, 518, 146, 274, 530, 162, 290, 546, 386, 28, 44, 76, 100, 548, 580, 280, 104, 296, 400, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_93, vertices_581, vertices_409, vertices_361, vertices_657, vertices_961, vertices_286, vertices_302, vertices_550, vertices_690, vertices_402, vertices_482, vertices_108, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_25, vertices_73, vertices_265, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_270, vertices_22, vertices_38, vertices_518, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_44, vertices_76, vertices_100, vertices_548, vertices_580, vertices_280, vertices_104, vertices_296, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_93), (false, vertices_581), (false, vertices_409), (false, vertices_361), (false, vertices_657), (false, vertices_961), (true, vertices_270), (true, vertices_38), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_44), (true, vertices_100), (true, vertices_548), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_270) then 16 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_2 0 0 1 2 7 270
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 0 4 5 6 7 482 162 2
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 270 286 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 270 302 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 690
cert_cover_5 3 1 0 3 4 6 146 690 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 482
cert_cover_5 5 2 0 4 5 6 162 482 2
cert_coverFacet 6 108
cert_cover_2 6 2 1 4 5 44 108 3
cert_coverFacet 7 740
cert_cover_5 7 3 1 4 5 6 100 740 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1049

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_1050.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1050

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [27, 299, 339, 557, 601, 737, 353, 158, 398, 722, 450, 540, 300, 692, 484, 11, 19, 259, 25, 41, 521, 81, 97, 289, 545, 321, 577, 142, 26, 266, 82, 146, 194, 322, 386, 28, 44, 268, 524, 148, 532, 164, 292, 548, 388, 536, 296, 592, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_27, vertices_299, vertices_339, vertices_557, vertices_601, vertices_737, vertices_353, vertices_158, vertices_398, vertices_722, vertices_450, vertices_540, vertices_300, vertices_692, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_25, vertices_41, vertices_521, vertices_81, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_142, vertices_26, vertices_266, vertices_82, vertices_146, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_268, vertices_524, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_536, vertices_296, vertices_592, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_27), (false, vertices_299), (false, vertices_339), (false, vertices_557), (false, vertices_601), (false, vertices_737), (false, vertices_353), (true, vertices_142), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_28), (true, vertices_268), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (false, vertices_353) then 1 else
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
  | 0 => Sum.inr ⟨(false, vertices_27), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
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
  | 15 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1050

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_1051.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1051

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 647, 179, 101, 837, 361, 929, 30, 590, 538, 914, 60, 108, 440, 856, 7, 51, 131, 37, 69, 517, 97, 161, 289, 321, 641, 769, 14, 22, 518, 26, 522, 146, 530, 642, 28, 44, 76, 52, 100, 580, 56, 280, 536, 104, 296, 328, 584, 176, 400, 784, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_647, vertices_179, vertices_101, vertices_837, vertices_361, vertices_929, vertices_30, vertices_590, vertices_538, vertices_914, vertices_60, vertices_108, vertices_440, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_51, vertices_131, vertices_37, vertices_69, vertices_517, vertices_97, vertices_161, vertices_289, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_518, vertices_26, vertices_522, vertices_146, vertices_530, vertices_642, vertices_28, vertices_44, vertices_76, vertices_52, vertices_100, vertices_580, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_584, vertices_176, vertices_400, vertices_784, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_647), (false, vertices_179), (false, vertices_101), (false, vertices_837), (false, vertices_361), (false, vertices_929), (true, vertices_14), (true, vertices_26), (true, vertices_522), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_584), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 15 else
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_101) then 0 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 0 3 6 7 8 914 146 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 2 3 5 7 8 856 280 2
cert_rows
cert_pivot_2 1 0 4 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 5 14 590 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 914
cert_cover_5 3 1 0 3 6 7 146 914 3
cert_coverFacet 4 60
cert_cover_2 4 2 1 3 4 28 60 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 440
cert_cover_5 6 2 2 3 4 6 56 440 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 280 856 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1051

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_1052.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1052

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 835, 387, 597, 665, 809, 393, 310, 342, 426, 178, 684, 180, 660, 868, 67, 131, 259, 137, 265, 521, 81, 145, 529, 577, 385, 769, 278, 50, 82, 146, 162, 290, 322, 386, 52, 84, 148, 532, 164, 292, 548, 324, 580, 644, 168, 296, 552, 392, 648, 176, 656, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_835, vertices_387, vertices_597, vertices_665, vertices_809, vertices_393, vertices_310, vertices_342, vertices_426, vertices_178, vertices_684, vertices_180, vertices_660, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_577, vertices_385, vertices_769, vertices_278, vertices_50, vertices_82, vertices_146, vertices_162, vertices_290, vertices_322, vertices_386, vertices_52, vertices_84, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_644, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_176, vertices_656, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_835), (false, vertices_387), (false, vertices_597), (false, vertices_665), (false, vertices_809), (false, vertices_393), (true, vertices_278), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_52), (true, vertices_148), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_644), (true, vertices_168), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (true, vertices_278) then 17 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_176) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_278), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 7 278
cert_row_4 1 0 2 4 6 7 426 162 1
cert_row_4 2 1 2 4 6 8 684 164 1
cert_row_4 3 1 4 5 7 8 868 292 2
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 278 310 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 5 278 342 3
cert_coverFacet 2 426
cert_cover_5 2 1 0 2 4 6 162 426 1
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 684
cert_cover_5 4 2 1 2 4 6 164 684 1
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 292 868 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1052

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_1053.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1053

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 557, 421, 665, 169, 961, 310, 566, 346, 722, 834, 312, 568, 216, 488, 37, 261, 517, 41, 137, 521, 161, 385, 641, 769, 54, 262, 518, 82, 274, 530, 322, 578, 770, 292, 548, 56, 88, 152, 280, 536, 168, 296, 552, 200, 328, 304, 560, 208, 656, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_557, vertices_421, vertices_665, vertices_169, vertices_961, vertices_310, vertices_566, vertices_346, vertices_722, vertices_834, vertices_312, vertices_568, vertices_216, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_41, vertices_137, vertices_521, vertices_161, vertices_385, vertices_641, vertices_769, vertices_54, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_292, vertices_548, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_304, vertices_560, vertices_208, vertices_656, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_557), (false, vertices_421), (false, vertices_665), (false, vertices_169), (false, vertices_961), (true, vertices_54), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_304), (true, vertices_560), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_54) then 17 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 0 2 3 5 7 346 82 1
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 0 0 1 3 8 54 566 3
cert_coverFacet 2 346
cert_cover_5 2 2 0 2 3 5 82 346 1
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 82 722 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 168 488 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1053

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_1054.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1054

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 565, 213, 901, 601, 457, 678, 362, 618, 434, 898, 180, 368, 624, 464, 21, 133, 517, 73, 265, 521, 81, 529, 193, 385, 769, 106, 266, 522, 162, 290, 546, 386, 642, 770, 52, 148, 164, 548, 644, 328, 584, 112, 176, 304, 560, 208, 336, 592, 400, 352, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_565, vertices_213, vertices_901, vertices_601, vertices_457, vertices_678, vertices_362, vertices_618, vertices_434, vertices_898, vertices_180, vertices_368, vertices_624, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_529, vertices_193, vertices_385, vertices_769, vertices_106, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_164, vertices_548, vertices_644, vertices_328, vertices_584, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_565), (false, vertices_213), (false, vertices_901), (false, vertices_601), (false, vertices_457), (true, vertices_106), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_162) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
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
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 3 4 6 7 434 162 1
cert_rows_3
cert_pivot_3 1 2 0
cert_heightProof 3
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 7 106 362 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 434
cert_cover_5 3 2 0 3 4 6 162 434 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 180
cert_cover_2 5 3 1 4 6 52 180 3
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1054

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_1055.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1055

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 595, 589, 569, 233, 433, 838, 458, 818, 402, 172, 556, 332, 396, 932, 83, 41, 73, 521, 49, 145, 529, 161, 193, 577, 146, 274, 530, 194, 322, 578, 386, 770, 44, 76, 140, 268, 524, 164, 548, 324, 580, 388, 772, 168, 552, 200, 328, 392, 304, 560, 400, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_595, vertices_589, vertices_569, vertices_233, vertices_433, vertices_838, vertices_458, vertices_818, vertices_402, vertices_172, vertices_556, vertices_332, vertices_396, vertices_932] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_41, vertices_73, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_193, vertices_577, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_44, vertices_76, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_772, vertices_168, vertices_552, vertices_200, vertices_328, vertices_392, vertices_304, vertices_560, vertices_400, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_595), (false, vertices_589), (false, vertices_569), (false, vertices_233), (false, vertices_433), (true, vertices_274), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_548), (true, vertices_324), (true, vertices_388), (true, vertices_772), (true, vertices_328), (true, vertices_392), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 16 else
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 2 5 6 7 458 194 1
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 194 458 1
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 274 818 2
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 932
cert_cover_5 8 3 1 4 6 7 164 932 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1055

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_1057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 661, 453, 601, 209, 865, 654, 390, 186, 618, 434, 802, 376, 664, 464, 133, 261, 517, 81, 145, 529, 193, 321, 577, 769, 134, 262, 518, 42, 138, 522, 178, 290, 546, 386, 770, 388, 644, 56, 88, 152, 536, 104, 584, 648, 304, 208, 336, 400, 656, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_661, vertices_453, vertices_601, vertices_209, vertices_865, vertices_654, vertices_390, vertices_186, vertices_618, vertices_434, vertices_802, vertices_376, vertices_664, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_522, vertices_178, vertices_290, vertices_546, vertices_386, vertices_770, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_584, vertices_648, vertices_304, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_661), (false, vertices_453), (false, vertices_601), (false, vertices_209), (false, vertices_865), (true, vertices_134), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_178), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_56), (true, vertices_152), (true, vertices_104), (true, vertices_648), (true, vertices_304), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_178) then 17 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 209 134 42 138 522 290 546 386 56 152 104 648 304 336 400 775 178 661 453 601 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 0 3 4 6 178
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 186
cert_cover_5 2 1 0 2 3 4 42 186 2
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 42 618 3
cert_coverFacet 4 434
cert_cover_5 4 1 0 3 4 7 178 434 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1057

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_1058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 805, 901, 361, 713, 625, 406, 602, 330, 650, 690, 338, 372, 180, 676, 773, 73, 137, 265, 97, 289, 545, 577, 385, 641, 74, 138, 266, 522, 82, 146, 274, 530, 322, 386, 642, 52, 148, 276, 164, 292, 548, 388, 644, 328, 584, 648, 112, 176, 560, 336, 592, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_805, vertices_901, vertices_361, vertices_713, vertices_625, vertices_406, vertices_602, vertices_330, vertices_650, vertices_690, vertices_338, vertices_372, vertices_180, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_773, vertices_73, vertices_137, vertices_265, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_386, vertices_642, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_328, vertices_584, vertices_648, vertices_112, vertices_176, vertices_560, vertices_336, vertices_592, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_805), (false, vertices_901), (false, vertices_361), (false, vertices_713), (false, vertices_625), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_642), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_176), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 74 1 522 2 82 146 274 530 322 642 52 148 276 164 176 336 672 395 805 901 361 713 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 74 2
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 74 602 2
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 146 690 2
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 52 372 3
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1058

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_1059.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1059

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 661, 185, 601, 361, 225, 902, 842, 434, 226, 354, 572, 812, 308, 404, 25, 41, 73, 145, 529, 97, 161, 193, 577, 641, 98, 162, 290, 194, 322, 578, 386, 642, 770, 556, 52, 148, 276, 532, 292, 388, 644, 772, 56, 536, 296, 328, 584, 776, 176, 304, 400, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_661, vertices_185, vertices_601, vertices_361, vertices_225, vertices_902, vertices_842, vertices_434, vertices_226, vertices_354, vertices_572, vertices_812, vertices_308, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_145, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_641, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_556, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_388, vertices_644, vertices_772, vertices_56, vertices_536, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_400, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_661), (false, vertices_185), (false, vertices_601), (false, vertices_361), (false, vertices_225), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_556), (true, vertices_52), (true, vertices_276), (true, vertices_292), (true, vertices_388), (true, vertices_772), (true, vertices_776), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_556) then 19 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 225 2 98 1 162 290 322 386 770 52 276 292 388 772 776 304 400 707 661 556 185 601 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_2 1 1 2 4 8 556
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 0 3 4 6 7 434 162 1
cert_rows
cert_pivot_2 5 2 1 0
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 322 842 1
cert_coverFacet 2 434
cert_cover_5 2 3 0 3 4 6 162 434 1
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 572
cert_cover_5 5 1 1 2 3 4 556 572 2
cert_coverFacet 6 812
cert_cover_5 6 1 1 2 4 7 556 812 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1059

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_1060.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1060

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 597, 789, 409, 809, 713, 118, 682, 178, 866, 706, 436, 356, 836, 424, 533, 137, 265, 521, 81, 145, 273, 193, 577, 769, 50, 82, 146, 98, 162, 546, 194, 578, 642, 52, 84, 276, 100, 292, 324, 580, 772, 168, 296, 552, 392, 648, 176, 400, 352, 416, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_597, vertices_789, vertices_409, vertices_809, vertices_713, vertices_118, vertices_682, vertices_178, vertices_866, vertices_706, vertices_436, vertices_356, vertices_836, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_193, vertices_577, vertices_769, vertices_50, vertices_82, vertices_146, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_52, vertices_84, vertices_276, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_176, vertices_400, vertices_352, vertices_416, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_597), (false, vertices_789), (false, vertices_409), (false, vertices_809), (false, vertices_713), (true, vertices_50), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_642), (true, vertices_52), (true, vertices_100), (true, vertices_292), (true, vertices_324), (true, vertices_168), (true, vertices_176), (true, vertices_352), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 16 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 50 2 98 1 162 546 578 642 52 100 292 324 168 176 352 416 832 211 597 789 409 809 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 0 1 3 4 5 118 50 1
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 50 118 1
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 162 682 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 98 866 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 436
cert_cover_5 5 3 1 3 4 6 52 436 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1060

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_1061.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1061

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 301, 557, 661, 453, 793, 337, 678, 618, 850, 658, 226, 420, 488, 840, 45, 133, 261, 517, 265, 521, 81, 145, 273, 529, 193, 321, 82, 146, 530, 98, 162, 546, 194, 578, 642, 164, 292, 548, 388, 644, 104, 296, 552, 328, 584, 776, 336, 656, 784, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_301, vertices_557, vertices_661, vertices_453, vertices_793, vertices_337, vertices_678, vertices_618, vertices_850, vertices_658, vertices_226, vertices_420, vertices_488, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_133, vertices_261, vertices_517, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_336, vertices_656, vertices_784, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_301), (false, vertices_557), (false, vertices_661), (false, vertices_453), (false, vertices_793), (false, vertices_337), (true, vertices_530), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_642), (true, vertices_164), (true, vertices_104), (true, vertices_328), (true, vertices_584), (true, vertices_224), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 20 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
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
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 2 4 5 8 618 98 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 98 618 1
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 82 850 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1061

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_1062.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1062

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 451, 579, 229, 409, 625, 177, 358, 806, 610, 796, 460, 652, 676, 696, 67, 259, 515, 49, 145, 273, 529, 97, 161, 193, 577, 385, 294, 98, 546, 322, 578, 770, 140, 268, 524, 100, 164, 548, 196, 324, 644, 772, 152, 280, 536, 392, 648, 176, 560, 784, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_451, vertices_579, vertices_229, vertices_409, vertices_625, vertices_177, vertices_358, vertices_806, vertices_610, vertices_796, vertices_460, vertices_652, vertices_676, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_385, vertices_294, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_644, vertices_772, vertices_152, vertices_280, vertices_536, vertices_392, vertices_648, vertices_176, vertices_560, vertices_784, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_451), (false, vertices_579), (false, vertices_229), (false, vertices_409), (false, vertices_625), (false, vertices_177), (true, vertices_294), (true, vertices_98), (true, vertices_546), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_648), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_229) then 15 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (true, vertices_294) then 16 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 1 579 0 177 98 546 140 268 524 548 324 644 772 536 648 672 229 294 787 451 409 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 7 294
cert_row_4 1 1 2 5 6 7 460 140 2
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 294 358 3
cert_coverFacet 1 806
cert_cover_5 1 0 0 1 4 8 294 806 3
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 268 796 2
cert_coverFacet 4 460
cert_cover_5 4 1 1 2 5 6 140 460 2
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 152 696 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1062

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_1063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 341, 313, 601, 681, 353, 454, 426, 722, 354, 674, 796, 908, 212, 660, 25, 41, 521, 81, 273, 97, 289, 545, 321, 577, 98, 162, 290, 546, 194, 322, 578, 386, 642, 780, 84, 148, 276, 532, 196, 324, 388, 644, 280, 536, 168, 296, 392, 648, 208, 592, 656, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_341, vertices_313, vertices_601, vertices_681, vertices_353, vertices_454, vertices_426, vertices_722, vertices_354, vertices_674, vertices_796, vertices_908, vertices_212, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_521, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_780, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_648, vertices_208, vertices_592, vertices_656, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_341), (false, vertices_313), (false, vertices_601), (false, vertices_681), (false, vertices_353), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_780), (true, vertices_148), (true, vertices_532), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_392), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_780) then 19 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 353 2 162 1 290 194 322 386 642 148 532 196 388 644 392 208 656 611 341 780 313 601 681
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 162 1
cert_row_2 1 1 2 7 8 780
cert_row_4 2 0 1 5 6 7 454 194 1
cert_row_4 3 0 3 5 6 8 722 194 1
cert_rows
cert_pivot_2 4 2 1 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 2 0 1 5 6 194 454 1
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 162 426 1
cert_coverFacet 2 722
cert_cover_5 2 3 0 3 5 6 194 722 1
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 796
cert_cover_5 5 1 1 2 3 7 780 796 2
cert_coverFacet 6 908
cert_cover_5 6 1 1 2 6 7 780 908 2
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1063

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_1064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 677, 901, 617, 457, 241, 790, 602, 202, 394, 434, 210, 628, 308, 420, 645, 73, 265, 521, 97, 161, 545, 193, 385, 769, 74, 138, 266, 522, 82, 146, 274, 530, 194, 386, 770, 52, 276, 532, 164, 292, 548, 388, 772, 200, 584, 392, 112, 176, 304, 208, 592, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_677, vertices_901, vertices_617, vertices_457, vertices_241, vertices_790, vertices_602, vertices_202, vertices_394, vertices_434, vertices_210, vertices_628, vertices_308, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_645, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_385, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_386, vertices_770, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_200, vertices_584, vertices_392, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_677), (false, vertices_901), (false, vertices_617), (false, vertices_457), (false, vertices_241), (true, vertices_74), (true, vertices_138), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_304), (true, vertices_592), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 74 1 138 2 82 146 274 530 194 386 52 276 532 292 304 592 416 779 677 901 617 457 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 74 2
cert_row_4 1 0 3 4 6 7 434 146 2
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 74 602 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 434
cert_cover_5 4 1 0 3 4 6 146 434 2
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1064

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3603 : Certifies 3603 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3604 : Certifies 3604 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3605 : Certifies 3605 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3606 : Certifies 3606 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3607 : Certifies 3607 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3608 : Certifies 3608 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3609 : Certifies 3609 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3610 : Certifies 3610 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3611 : Certifies 3611 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3612 : Certifies 3612 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1043.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3613 : Certifies 3613 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1044.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3614 : Certifies 3614 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1045.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3615 : Certifies 3615 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3616 : Certifies 3616 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1047.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3617 : Certifies 3617 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1048.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3618 : Certifies 3618 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1049.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3619 : Certifies 3619 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1050.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3620 : Certifies 3620 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1051.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3621 : Certifies 3621 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1052.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3622 : Certifies 3622 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1053.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3623 : Certifies 3623 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1054.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3624 : Certifies 3624 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1055.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3625 : Certifies 3625 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3626 : Certifies 3626 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3627 : Certifies 3627 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1059.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3628 : Certifies 3628 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1060.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3629 : Certifies 3629 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1061.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3630 : Certifies 3630 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1062.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3631 : Certifies 3631 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3632 : Certifies 3632 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B119 (j : Fin 30) :
    Certifies (3603 + j.val) := by
  fin_cases j
  · exact projection_3603
  · exact projection_3604
  · exact projection_3605
  · exact projection_3606
  · exact projection_3607
  · exact projection_3608
  · exact projection_3609
  · exact projection_3610
  · exact projection_3611
  · exact projection_3612
  · exact projection_3613
  · exact projection_3614
  · exact projection_3615
  · exact projection_3616
  · exact projection_3617
  · exact projection_3618
  · exact projection_3619
  · exact projection_3620
  · exact projection_3621
  · exact projection_3622
  · exact projection_3623
  · exact projection_3624
  · exact projection_3625
  · exact projection_3626
  · exact projection_3627
  · exact projection_3628
  · exact projection_3629
  · exact projection_3630
  · exact projection_3631
  · exact projection_3632

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
