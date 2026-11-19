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
/- Source: ProjectionCertificates/P0_145.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_145

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 285, 597, 453, 537, 777, 737, 302, 682, 778, 482, 124, 356, 632, 21, 69, 261, 25, 265, 521, 529, 193, 577, 385, 641, 769, 42, 266, 522, 162, 290, 386, 642, 770, 28, 44, 268, 84, 100, 292, 324, 120, 536, 552, 776, 592, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_285, vertices_597, vertices_453, vertices_537, vertices_777, vertices_737, vertices_302, vertices_682, vertices_778, vertices_482, vertices_124, vertices_356, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_25, vertices_265, vertices_521, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_42, vertices_266, vertices_522, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_84, vertices_100, vertices_292, vertices_324, vertices_120, vertices_536, vertices_552, vertices_776, vertices_592, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_285), (false, vertices_597), (false, vertices_453), (false, vertices_537), (false, vertices_777), (false, vertices_737), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_44), (true, vertices_100), (true, vertices_292), (true, vertices_120), (true, vertices_552), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_285) then 15 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_537) then 10 else
  if p.val = (false, vertices_777) then 11 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_120) then 19 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
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
cert_row_4 0 0 2 4 7 1 302 42 3
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 4 5 6 7 0 482 224 3
cert_row_2 3 3 4 5 2 120
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 42 302 1
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 42 682 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 162 482 2
cert_coverFacet 4 124
cert_cover_5 4 3 1 2 3 4 28 124 3
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 8 120 632 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_145

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_146.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_146

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 179, 275, 789, 613, 665, 673, 154, 794, 458, 482, 844, 356, 744, 19, 35, 259, 37, 261, 517, 145, 273, 529, 161, 545, 641, 26, 138, 266, 146, 274, 162, 290, 450, 100, 292, 324, 580, 772, 152, 536, 200, 328, 584, 648, 776, 784, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_179, vertices_275, vertices_789, vertices_613, vertices_665, vertices_673, vertices_154, vertices_794, vertices_458, vertices_482, vertices_844, vertices_356, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_37, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_641, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_162, vertices_290, vertices_450, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_179), (false, vertices_275), (false, vertices_789), (false, vertices_613), (false, vertices_665), (false, vertices_673), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_450), (true, vertices_324), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_275) then 10 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_673) then 11 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_450) then 18 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 7 8 3 794 266 3
cert_row_4 1 2 5 7 8 1 844 328 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 5 6 7 0 450
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 154
cert_cover_2 0 2 0 3 6 26 154 3
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 26 794 3
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 138 458 2
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 162 482 2
cert_coverFacet 4 844
cert_cover_5 4 1 1 2 5 7 324 844 1
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 200 744 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_146

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_147.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_147

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [163, 803, 707, 421, 841, 465, 182, 566, 658, 348, 540, 812, 404, 728, 35, 131, 515, 161, 289, 193, 321, 577, 385, 769, 54, 146, 530, 162, 546, 642, 28, 268, 524, 148, 276, 532, 164, 292, 548, 388, 88, 536, 328, 584, 776, 208, 336, 400, 656, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_163, vertices_803, vertices_707, vertices_421, vertices_841, vertices_465, vertices_182, vertices_566, vertices_658, vertices_348, vertices_540, vertices_812, vertices_404, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_54, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_88, vertices_536, vertices_328, vertices_584, vertices_776, vertices_208, vertices_336, vertices_400, vertices_656, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_163), (false, vertices_803), (false, vertices_707), (false, vertices_421), (false, vertices_841), (false, vertices_465), (true, vertices_54), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_88), (true, vertices_536), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_163) then 12 else
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_421) then 14 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 8 6 728 88 3
cert_row_4 1 1 2 3 7 5 348 28 3
cert_row_4 2 1 4 7 8 2 812 292 3
cert_row_2 3 1 3 4 0 54
cert_rows
cert_pivot_2 6 5 2 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 3 0 1 3 6 54 182 3
cert_coverFacet 1 566
cert_cover_5 1 3 0 1 3 8 54 566 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 348
cert_cover_5 3 1 1 2 3 5 28 348 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 812
cert_cover_5 5 2 1 2 4 7 268 812 2
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 728
cert_cover_5 7 0 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_147

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_149.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_149

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 355, 899, 661, 409, 337, 614, 810, 124, 156, 556, 908, 596, 376, 67, 259, 515, 81, 145, 273, 529, 321, 385, 641, 98, 290, 546, 578, 770, 28, 44, 140, 524, 84, 148, 532, 100, 548, 580, 644, 120, 152, 280, 296, 552, 392, 776, 336, 592, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_355, vertices_899, vertices_661, vertices_409, vertices_337, vertices_614, vertices_810, vertices_124, vertices_156, vertices_556, vertices_908, vertices_596, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_580, vertices_644, vertices_120, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_776, vertices_336, vertices_592, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_355), (false, vertices_899), (false, vertices_661), (false, vertices_409), (false, vertices_337), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_120), (true, vertices_296), (true, vertices_552), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_355) then 15 else
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_337) then 12 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_120) then 21 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 7 8 6 908 524 2
cert_row_4 1 0 4 5 8 1 614 98 3
cert_row_4 2 2 4 7 8 0 810 296 3
cert_row_2 3 3 4 5 2 120
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 290 810 1
cert_coverFacet 2 124
cert_cover_5 2 3 1 2 3 4 28 124 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 908
cert_cover_5 5 0 1 2 6 7 140 908 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 7 120 376 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_149

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_151.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_151

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 837, 217, 793, 617, 449, 174, 558, 790, 454, 154, 538, 740, 232, 25, 73, 521, 145, 273, 193, 321, 577, 385, 769, 46, 134, 262, 518, 26, 138, 522, 146, 274, 530, 386, 164, 548, 196, 324, 580, 772, 152, 536, 104, 168, 552, 200, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_837, vertices_217, vertices_793, vertices_617, vertices_449, vertices_174, vertices_558, vertices_790, vertices_454, vertices_154, vertices_538, vertices_740, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_521, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_837), (false, vertices_217), (false, vertices_793), (false, vertices_617), (false, vertices_449), (true, vertices_46), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_530), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_168), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_449) then 12 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_4 0 0 1 7 8 3 790 262 3
cert_row_4 1 0 1 5 6 7 454 134 2
cert_row_4 2 1 4 6 8 5 740 164 3
cert_row_2 3 1 2 4 0 46
cert_rows
cert_pivot_2 3 7 5 0
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 3 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 3 0 1 2 8 46 558 3
cert_coverFacet 2 790
cert_cover_5 2 0 0 1 3 7 262 790 2
cert_coverFacet 3 454
cert_cover_5 3 1 0 1 5 6 134 454 2
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 538
cert_cover_2 5 2 0 3 8 26 538 3
cert_coverFacet 6 740
cert_cover_5 6 2 1 4 5 6 164 740 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_151

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_152.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_152

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 781, 613, 421, 121, 313, 902, 218, 394, 778, 738, 676, 408, 496, 37, 261, 517, 57, 73, 265, 521, 97, 289, 577, 74, 138, 266, 522, 194, 578, 386, 642, 770, 164, 548, 388, 644, 772, 88, 152, 280, 392, 776, 112, 304, 208, 400, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_781, vertices_613, vertices_421, vertices_121, vertices_313, vertices_902, vertices_218, vertices_394, vertices_778, vertices_738, vertices_676, vertices_408, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_57, vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_577, vertices_74, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_392, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_781), (false, vertices_613), (false, vertices_421), (false, vertices_121), (false, vertices_313), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_152), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 138 1 266 2 194 386 642 770 644 152 392 208 400 224 672 587 781 613 421 121 313
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 6 7 8 1 902 386 3
cert_row_4 1 0 3 5 6 2 218 194 1
cert_row_4 2 4 5 6 8 0 738 224 3
cert_row_4 3 4 5 6 7 3 496 224 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 74 218 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_152

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_153.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_153

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 781, 213, 453, 601, 361, 150, 422, 774, 810, 626, 178, 616, 496, 21, 197, 261, 517, 73, 265, 521, 81, 529, 321, 22, 134, 262, 518, 50, 146, 530, 162, 290, 546, 770, 148, 388, 772, 104, 296, 552, 584, 776, 112, 176, 208, 592, 352, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_781, vertices_213, vertices_453, vertices_601, vertices_361, vertices_150, vertices_422, vertices_774, vertices_810, vertices_626, vertices_178, vertices_616, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_197, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_529, vertices_321, vertices_22, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_148, vertices_388, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_352, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_781), (false, vertices_213), (false, vertices_453), (false, vertices_601), (false, vertices_361), (true, vertices_134), (true, vertices_262), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_552), (true, vertices_112), (true, vertices_176), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 134 1 262 2 50 146 162 290 546 770 552 112 176 608 416 535 781 213 453 601 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 1 422 162 3
cert_row_4 1 0 4 7 8 2 810 290 3
cert_row_4 2 3 4 5 8 0 626 112 3
cert_row_4 3 4 5 6 7 3 496 352 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 422
cert_cover_5 1 0 0 1 4 6 134 422 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 290 810 1
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 616
cert_cover_2 6 4 2 5 8 104 616 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_153

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_154.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_154

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 341, 805, 709, 121, 617, 902, 58, 154, 810, 650, 466, 452, 728, 69, 261, 517, 105, 49, 81, 273, 289, 545, 577, 26, 42, 138, 522, 50, 146, 274, 290, 386, 642, 770, 196, 324, 388, 644, 772, 56, 88, 152, 552, 584, 648, 208, 336, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_341, vertices_805, vertices_709, vertices_121, vertices_617, vertices_902, vertices_58, vertices_154, vertices_810, vertices_650, vertices_466, vertices_452, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_105, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_146, vertices_274, vertices_290, vertices_386, vertices_642, vertices_770, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_552, vertices_584, vertices_648, vertices_208, vertices_336, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_341), (false, vertices_805), (false, vertices_709), (false, vertices_121), (false, vertices_617), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_388), (true, vertices_152), (true, vertices_648), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 14 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 26 1 42 2 138 522 146 386 642 770 388 152 648 208 448 307 341 805 709 121 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 6 7 8 1 902 386 3
cert_row_4 1 0 2 7 8 4 810 522 2
cert_row_4 2 3 5 6 7 0 466 208 3
cert_row_4 3 3 5 6 8 2 728 208 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 42 810 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 466
cert_cover_5 5 2 0 3 5 6 146 466 2
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_154

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_155.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_155

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 195, 835, 805, 457, 433, 218, 602, 658, 572, 412, 844, 308, 688, 67, 131, 515, 161, 289, 545, 193, 321, 385, 769, 90, 146, 530, 194, 578, 642, 28, 268, 524, 52, 276, 292, 548, 772, 152, 536, 200, 328, 584, 392, 176, 304, 560, 400, 656, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_195, vertices_835, vertices_805, vertices_457, vertices_433, vertices_218, vertices_602, vertices_658, vertices_572, vertices_412, vertices_844, vertices_308, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_90, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_772, vertices_152, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_195), (false, vertices_835), (false, vertices_805), (false, vertices_457), (false, vertices_433), (true, vertices_90), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_152), (true, vertices_536), (true, vertices_584), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 15 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_195) then 12 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_457) then 16 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
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
cert_row_4 0 1 2 3 8 4 572 28 3
cert_row_4 1 1 2 3 7 6 412 28 3
cert_row_4 2 2 5 7 8 1 844 328 3
cert_row_2 3 2 3 5 0 90
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 3 0 2 3 6 90 218 3
cert_coverFacet 1 602
cert_cover_5 1 3 0 2 3 8 90 602 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 572
cert_cover_5 3 0 1 2 3 4 28 572 3
cert_coverFacet 4 412
cert_cover_5 4 1 1 2 3 6 28 412 3
cert_coverFacet 5 844
cert_cover_5 5 2 1 2 5 7 268 844 2
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_155

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_156.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_156

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 805, 841, 689, 209, 481, 142, 782, 182, 566, 218, 586, 460, 420, 81, 145, 529, 161, 289, 545, 193, 321, 577, 769, 14, 54, 134, 518, 74, 138, 522, 82, 146, 530, 578, 140, 268, 164, 292, 548, 388, 772, 200, 328, 584, 776, 176, 560, 208, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_805, vertices_841, vertices_689, vertices_209, vertices_481, vertices_142, vertices_782, vertices_182, vertices_566, vertices_218, vertices_586, vertices_460, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_54, vertices_134, vertices_518, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_578, vertices_140, vertices_268, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_200, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_208, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_805), (false, vertices_841), (false, vertices_689), (false, vertices_209), (false, vertices_481), (true, vertices_14), (true, vertices_54), (true, vertices_134), (true, vertices_518), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_388), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_209) then 12 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_200) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 14 3
cert_row_4 1 1 2 5 6 7 460 140 2
cert_row_4 2 0 3 5 6 2 218 82 3
cert_row_2 3 1 3 4 0 54
cert_rows
cert_pivot_2 8 7 2 0
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 7 14 782 3
cert_coverFacet 2 182
cert_cover_5 2 3 0 1 3 6 54 182 3
cert_coverFacet 3 566
cert_cover_5 3 3 0 1 3 8 54 566 3
cert_coverFacet 4 218
cert_cover_5 4 2 0 2 3 5 74 218 2
cert_coverFacet 5 586
cert_cover_2 5 2 0 5 8 74 586 3
cert_coverFacet 6 460
cert_cover_5 6 1 1 2 5 6 140 460 2
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_156

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_157.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_157

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 781, 405, 709, 817, 209, 206, 590, 186, 810, 562, 210, 428, 432, 133, 261, 517, 81, 145, 273, 529, 193, 577, 769, 78, 42, 138, 522, 50, 82, 146, 530, 546, 194, 578, 140, 268, 524, 196, 580, 388, 168, 296, 776, 176, 304, 560, 208, 400, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_781, vertices_405, vertices_709, vertices_817, vertices_209, vertices_206, vertices_590, vertices_186, vertices_810, vertices_562, vertices_210, vertices_428, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_769, vertices_78, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_530, vertices_546, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_388, vertices_168, vertices_296, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_400, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_781), (false, vertices_405), (false, vertices_709), (false, vertices_817), (false, vertices_209), (true, vertices_78), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_546), (true, vertices_194), (true, vertices_140), (true, vertices_168), (true, vertices_296), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_209) then 12 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 3 186 42 3
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 1 2 6 7 4 428 140 3
cert_row_2 3 1 2 5 0 78
cert_rows
cert_pivot_2 3 8 4 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 3 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 3 0 1 2 8 78 590 3
cert_coverFacet 2 186
cert_cover_5 2 0 0 2 3 4 42 186 2
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 42 810 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 428
cert_cover_5 6 2 1 2 4 6 140 428 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_157

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_158.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_158

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 61, 557, 405, 709, 241, 902, 810, 370, 450, 706, 796, 312, 464, 45, 21, 133, 517, 49, 145, 97, 545, 193, 577, 98, 290, 546, 194, 322, 578, 386, 642, 770, 28, 524, 276, 388, 644, 772, 56, 280, 296, 552, 776, 112, 304, 208, 336, 400, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_61, vertices_557, vertices_405, vertices_709, vertices_241, vertices_902, vertices_810, vertices_370, vertices_450, vertices_706, vertices_796, vertices_312, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_21, vertices_133, vertices_517, vertices_49, vertices_145, vertices_97, vertices_545, vertices_193, vertices_577, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_524, vertices_276, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_296, vertices_552, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_400, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_61), (false, vertices_557), (false, vertices_405), (false, vertices_709), (false, vertices_241), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 15 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_290) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority_12 290 2 194 1 322 386 642 770 772 280 296 776 304 336 448 611 61 557 405 709 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 6 902 770 1
cert_row_4 1 0 3 4 7 5 370 290 1
cert_row_4 2 2 4 7 8 0 810 296 3
cert_row_4 3 2 3 7 8 1 796 280 3
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 290 810 1
cert_coverFacet 2 370
cert_cover_5 2 1 0 3 4 5 98 370 1
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 796
cert_cover_5 5 3 1 2 3 7 28 796 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_158

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_159.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_159

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 173, 557, 789, 453, 409, 838, 154, 618, 202, 466, 786, 740, 232, 45, 133, 261, 517, 25, 137, 521, 273, 529, 385, 26, 74, 138, 522, 146, 274, 530, 194, 322, 578, 770, 164, 548, 196, 324, 580, 772, 152, 104, 168, 552, 200, 400, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_173, vertices_557, vertices_789, vertices_453, vertices_409, vertices_838, vertices_154, vertices_618, vertices_202, vertices_466, vertices_786, vertices_740, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_273, vertices_529, vertices_385, vertices_26, vertices_74, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_770, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_772, vertices_152, vertices_104, vertices_168, vertices_552, vertices_200, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_173), (false, vertices_557), (false, vertices_789), (false, vertices_453), (false, vertices_409), (true, vertices_74), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_580), (true, vertices_104), (true, vertices_200), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_409) then 16 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 74 2 138 1 146 274 194 322 578 770 580 104 200 224 608 539 409 173 557 789 453
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 8 2 618 578 1
cert_row_4 1 0 5 6 7 3 466 194 3
cert_row_4 2 1 5 7 8 0 838 324 3
cert_row_4 3 4 5 6 8 1 740 224 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 2 0 1 5 7 322 838 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 5 74 618 2
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 146 466 2
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_159

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_162.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_162

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 403, 163, 557, 793, 689, 230, 358, 210, 850, 300, 844, 724, 676, 35, 131, 259, 41, 265, 521, 145, 273, 529, 161, 545, 102, 82, 146, 274, 162, 290, 194, 322, 44, 268, 524, 164, 292, 548, 196, 324, 580, 644, 296, 776, 208, 592, 656, 784, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_403, vertices_163, vertices_557, vertices_793, vertices_689, vertices_230, vertices_358, vertices_210, vertices_850, vertices_300, vertices_844, vertices_724, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_102, vertices_82, vertices_146, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_44, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_296, vertices_776, vertices_208, vertices_592, vertices_656, vertices_784, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_403), (false, vertices_163), (false, vertices_557), (false, vertices_793), (false, vertices_689), (true, vertices_102), (true, vertices_82), (true, vertices_194), (true, vertices_322), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_644), (true, vertices_208), (true, vertices_592), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_403) then 19 else
  if p.val = (false, vertices_163) then 13 else
  if p.val = (false, vertices_557) then 15 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_102) then 16 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_4 0 1 5 7 8 2 844 324 3
cert_row_4 1 0 3 5 8 7 850 82 3
cert_row_4 2 1 5 6 8 3 724 196 3
cert_row_2 3 1 4 5 0 102
cert_rows
cert_pivot_2 2 7 3 0
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 3 0 1 4 6 102 230 3
cert_coverFacet 1 358
cert_cover_5 1 3 0 1 4 7 102 358 3
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 850
cert_cover_5 3 1 0 3 5 7 82 850 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 844
cert_cover_5 5 0 1 2 5 7 268 844 2
cert_coverFacet 6 724
cert_cover_5 6 2 1 3 5 6 196 724 1
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_162

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_165.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_165

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 203, 787, 643, 77, 653, 805, 690, 466, 364, 556, 744, 496, 816, 67, 131, 259, 515, 13, 69, 261, 517, 73, 137, 641, 769, 146, 274, 530, 194, 322, 642, 44, 76, 524, 292, 548, 324, 104, 552, 200, 648, 176, 304, 560, 464, 784, 224, 352, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_203, vertices_787, vertices_643, vertices_77, vertices_653, vertices_805, vertices_690, vertices_466, vertices_364, vertices_556, vertices_744, vertices_496, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_13, vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_641, vertices_769, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_642, vertices_44, vertices_76, vertices_524, vertices_292, vertices_548, vertices_324, vertices_104, vertices_552, vertices_200, vertices_648, vertices_176, vertices_304, vertices_560, vertices_464, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_203), (false, vertices_787), (false, vertices_643), (false, vertices_77), (false, vertices_653), (false, vertices_805), (true, vertices_146), (true, vertices_44), (true, vertices_104), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_464), (true, vertices_224), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_643) then 10 else
  if p.val = (false, vertices_77) then 11 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_805) then 18 else
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
  if p.val = (true, vertices_672) then 9 else
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
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
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
cert_row_4 1 2 4 5 7 1 364 104 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 5 6 7 3 464
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 690
cert_cover_5 0 0 0 3 4 6 146 690 2
cert_coverFacet 1 466
cert_cover_5 1 3 0 3 5 6 146 466 2
cert_coverFacet 2 364
cert_cover_5 2 1 1 2 4 5 44 364 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 176 496 2
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_165

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_166.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_166

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 781, 661, 389, 105, 457, 737, 790, 362, 778, 242, 690, 338, 468, 133, 261, 517, 41, 73, 265, 521, 97, 545, 193, 385, 641, 42, 266, 522, 178, 82, 274, 530, 98, 546, 322, 770, 148, 276, 532, 388, 772, 104, 328, 776, 208, 336, 656, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_781, vertices_661, vertices_389, vertices_105, vertices_457, vertices_737, vertices_790, vertices_362, vertices_778, vertices_242, vertices_690, vertices_338, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_545, vertices_193, vertices_385, vertices_641, vertices_42, vertices_266, vertices_522, vertices_178, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_104, vertices_328, vertices_776, vertices_208, vertices_336, vertices_656, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_781), (false, vertices_661), (false, vertices_389), (false, vertices_105), (false, vertices_457), (false, vertices_737), (true, vertices_266), (true, vertices_178), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_322), (true, vertices_770), (true, vertices_276), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_389) then 10 else
  if p.val = (false, vertices_105) then 11 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_178) then 14 else
  if p.val = (true, vertices_82) then 1 else
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
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 4 5 7 2 362 98 3
cert_row_4 2 3 5 6 7 1 468 208 3
cert_row_2 3 3 4 6 0 178
cert_rows
cert_pivot_2 8 2 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 362
cert_cover_5 1 1 0 2 4 5 42 362 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 242
cert_cover_5 3 3 0 3 4 5 178 242 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 8 178 690 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 468
cert_cover_5 6 2 1 3 5 6 148 468 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_166

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_170.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_170

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 405, 677, 837, 617, 225, 790, 122, 538, 842, 242, 402, 660, 696, 133, 261, 517, 97, 161, 545, 193, 321, 577, 385, 26, 74, 522, 114, 146, 274, 530, 194, 322, 386, 770, 148, 276, 532, 644, 772, 56, 536, 104, 552, 584, 176, 400, 656, 224, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_405, vertices_677, vertices_837, vertices_617, vertices_225, vertices_790, vertices_122, vertices_538, vertices_842, vertices_242, vertices_402, vertices_660, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_26, vertices_74, vertices_522, vertices_114, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_770, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_56, vertices_536, vertices_104, vertices_552, vertices_584, vertices_176, vertices_400, vertices_656, vertices_224, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_405), (false, vertices_677), (false, vertices_837), (false, vertices_617), (false, vertices_225), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_176), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_225) then 12 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_114) then 15 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 26 74 522 146 274 530 770 532 56 536 176 656 225 451 114 405 677 837 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 7 8 1 790 274 3
cert_row_4 1 0 2 5 8 7 842 74 3
cert_row_4 2 3 4 6 8 2 696 176 3
cert_row_2 3 3 4 5 0 114
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 122
cert_cover_5 1 3 0 2 3 4 26 122 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 74 842 3
cert_coverFacet 4 242
cert_cover_5 4 3 0 3 4 6 114 242 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 696
cert_cover_5 7 2 2 3 4 6 56 696 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_170

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_171.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_171

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 519, 595, 661, 421, 121, 185, 353, 902, 618, 354, 802, 728, 936, 7, 67, 515, 133, 261, 517, 57, 81, 145, 529, 97, 161, 289, 321, 262, 518, 98, 290, 546, 322, 578, 770, 388, 644, 88, 152, 104, 168, 552, 584, 648, 592, 656, 352, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_519, vertices_595, vertices_661, vertices_421, vertices_121, vertices_185, vertices_353, vertices_902, vertices_618, vertices_354, vertices_802, vertices_728, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_515, vertices_133, vertices_261, vertices_517, vertices_57, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_289, vertices_321, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_388, vertices_644, vertices_88, vertices_152, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_592, vertices_656, vertices_352, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_519), (false, vertices_595), (false, vertices_661), (false, vertices_421), (false, vertices_121), (false, vertices_185), (false, vertices_353), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_552), (true, vertices_584), (true, vertices_648), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_519) then 9 else
  if p.val = (false, vertices_595) then 13 else
  if p.val = (false, vertices_661) then 15 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_353) then 10 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 6 7 8 1 902 770 1
cert_row_4 1 2 4 5 8 0 618 104 3
cert_row_4 2 2 5 6 8 3 728 584 2
cert_row_4 3 4 6 7 8 2 936 416 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 262 902 2
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 98 618 1
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 728
cert_cover_5 4 2 2 3 5 6 88 728 3
cert_coverFacet 5 936
cert_cover_5 5 3 2 4 6 7 168 936 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_171

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_172.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_172

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 29, 205, 309, 229, 793, 617, 422, 714, 914, 226, 610, 668, 404, 13, 21, 37, 197, 25, 73, 521, 273, 97, 289, 545, 769, 98, 162, 290, 546, 194, 578, 386, 642, 770, 28, 140, 148, 276, 164, 292, 388, 536, 200, 584, 648, 400, 656, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_29, vertices_205, vertices_309, vertices_229, vertices_793, vertices_617, vertices_422, vertices_714, vertices_914, vertices_226, vertices_610, vertices_668, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_197, vertices_25, vertices_73, vertices_521, vertices_273, vertices_97, vertices_289, vertices_545, vertices_769, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_148, vertices_276, vertices_164, vertices_292, vertices_388, vertices_536, vertices_200, vertices_584, vertices_648, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_29), (false, vertices_205), (false, vertices_309), (false, vertices_229), (false, vertices_793), (false, vertices_617), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_388), (true, vertices_648), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_29) then 11 else
  if p.val = (false, vertices_205) then 16 else
  if p.val = (false, vertices_309) then 15 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_656) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 4 422 386 1
cert_row_4 1 0 2 6 8 5 714 642 1
cert_row_4 2 3 6 7 8 0 914 400 3
cert_row_4 3 2 3 6 8 1 668 536 2
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 162 422 1
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 194 714 1
cert_coverFacet 2 914
cert_cover_5 2 2 0 3 6 7 386 914 1
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 610
cert_cover_2 4 4 0 5 8 98 610 3
cert_coverFacet 5 668
cert_cover_5 5 3 1 2 3 6 28 668 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_172

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_173.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_173

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 93, 789, 709, 345, 481, 570, 434, 786, 738, 540, 620, 312, 360, 21, 69, 517, 89, 273, 193, 321, 385, 641, 769, 50, 274, 530, 162, 546, 386, 642, 770, 28, 76, 524, 532, 580, 56, 280, 536, 104, 296, 552, 328, 304, 784, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_93, vertices_789, vertices_709, vertices_345, vertices_481, vertices_570, vertices_434, vertices_786, vertices_738, vertices_540, vertices_620, vertices_312, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_89, vertices_273, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_50, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_532, vertices_580, vertices_56, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_304, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_93), (false, vertices_789), (false, vertices_709), (false, vertices_345), (false, vertices_481), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_524), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_304), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_4 1 0 2 4 8 3 570 546 1
cert_row_4 2 4 5 6 8 0 738 224 3
cert_row_4 3 2 4 5 8 1 620 104 3
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 1 0 2 3 4 50 570 1
cert_coverFacet 1 434
cert_cover_5 1 0 0 3 4 6 50 434 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 162 738 2
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 76 620 2
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_173

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_174.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_174

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 301, 405, 677, 817, 206, 398, 794, 586, 402, 738, 108, 228, 872, 37, 133, 261, 145, 273, 529, 289, 545, 641, 142, 74, 266, 522, 146, 274, 530, 194, 578, 386, 642, 44, 76, 268, 100, 164, 196, 388, 104, 296, 584, 776, 400, 784, 224, 608, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_301, vertices_405, vertices_677, vertices_817, vertices_206, vertices_398, vertices_794, vertices_586, vertices_402, vertices_738, vertices_108, vertices_228, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_641, vertices_142, vertices_74, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_44, vertices_76, vertices_268, vertices_100, vertices_164, vertices_196, vertices_388, vertices_104, vertices_296, vertices_584, vertices_776, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_301), (false, vertices_405), (false, vertices_677), (false, vertices_817), (true, vertices_142), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_76), (true, vertices_100), (true, vertices_196), (true, vertices_104), (true, vertices_584), (true, vertices_776), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 2 7 8 3 794 266 3
cert_row_4 1 2 4 5 8 7 872 104 3
cert_row_4 2 0 5 6 8 4 738 194 3
cert_row_2 3 1 2 6 0 142
cert_rows
cert_pivot_2 3 7 4 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 3 0 1 2 5 142 206 3
cert_coverFacet 1 398
cert_cover_5 1 3 0 1 2 7 142 398 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 266 794 2
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 194 738 1
cert_coverFacet 6 108
cert_cover_2 6 2 1 4 5 44 108 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 872
cert_cover_5 8 1 2 4 5 7 104 872 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_174

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_175.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_175

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 327, 51, 227, 597, 713, 689, 458, 306, 930, 332, 588, 908, 820, 263, 19, 35, 67, 21, 69, 49, 529, 161, 193, 577, 641, 50, 274, 162, 290, 194, 322, 386, 76, 268, 524, 276, 532, 324, 580, 772, 200, 328, 584, 392, 648, 304, 560, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_327, vertices_51, vertices_227, vertices_597, vertices_713, vertices_689, vertices_458, vertices_306, vertices_930, vertices_332, vertices_588, vertices_908, vertices_820] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_19, vertices_35, vertices_67, vertices_21, vertices_69, vertices_49, vertices_529, vertices_161, vertices_193, vertices_577, vertices_641, vertices_50, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_324, vertices_580, vertices_772, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_327), (false, vertices_51), (false, vertices_227), (false, vertices_597), (false, vertices_713), (false, vertices_689), (true, vertices_290), (true, vertices_386), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_772), (true, vertices_328), (true, vertices_392), (true, vertices_304), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 14 else
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_51) then 11 else
  if p.val = (false, vertices_227) then 13 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_290) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 5 458 386 1
cert_row_4 1 4 6 7 8 0 930 672 2
cert_row_4 2 1 6 7 8 2 908 772 1
cert_row_4 3 3 4 7 8 1 820 304 3
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 458
cert_cover_5 0 0 0 2 5 6 194 458 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 930
cert_cover_5 2 1 0 4 6 7 162 930 3
cert_coverFacet 3 332
cert_cover_2 3 2 1 5 7 76 332 3
cert_coverFacet 4 588
cert_cover_2 4 2 1 5 8 76 588 3
cert_coverFacet 5 908
cert_cover_5 5 2 1 2 6 7 268 908 2
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 276 820 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_175

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_176.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_176

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 653, 425, 841, 241, 705, 782, 182, 534, 422, 114, 850, 396, 724, 137, 265, 521, 97, 161, 289, 193, 321, 577, 641, 22, 166, 262, 518, 50, 82, 530, 98, 290, 322, 770, 140, 268, 524, 148, 532, 388, 644, 392, 776, 112, 176, 208, 592, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_653, vertices_425, vertices_841, vertices_241, vertices_705, vertices_782, vertices_182, vertices_534, vertices_422, vertices_114, vertices_850, vertices_396, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_22, vertices_166, vertices_262, vertices_518, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_322, vertices_770, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_388, vertices_644, vertices_392, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_653), (false, vertices_425), (false, vertices_841), (false, vertices_241), (false, vertices_705), (true, vertices_22), (true, vertices_166), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_770), (true, vertices_268), (true, vertices_148), (true, vertices_532), (true, vertices_388), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_705) then 12 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_166) then 15 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 22 262 518 50 82 530 770 268 148 532 388 592 705 355 166 653 425 841 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 2 782 262 3
cert_row_4 1 0 3 5 8 7 850 82 3
cert_row_4 2 1 5 6 8 3 724 644 1
cert_row_2 3 1 4 6 0 166
cert_rows
cert_pivot_2 2 7 3 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 182
cert_cover_5 1 3 0 1 3 4 22 182 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 422
cert_cover_5 3 3 0 1 4 7 166 422 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 850
cert_cover_5 5 1 0 3 5 7 82 850 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 724
cert_cover_5 7 2 1 3 5 6 148 724 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_176

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_177.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_177

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [23, 583, 51, 803, 213, 841, 369, 182, 678, 204, 588, 908, 472, 944, 7, 19, 35, 515, 21, 69, 49, 81, 289, 321, 577, 769, 22, 166, 518, 50, 546, 76, 140, 524, 148, 196, 580, 644, 200, 328, 584, 392, 776, 176, 304, 208, 336, 400, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_23, vertices_583, vertices_51, vertices_803, vertices_213, vertices_841, vertices_369, vertices_182, vertices_678, vertices_204, vertices_588, vertices_908, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_35, vertices_515, vertices_21, vertices_69, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_22, vertices_166, vertices_518, vertices_50, vertices_546, vertices_76, vertices_140, vertices_524, vertices_148, vertices_196, vertices_580, vertices_644, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_23), (false, vertices_583), (false, vertices_51), (false, vertices_803), (false, vertices_213), (false, vertices_841), (false, vertices_369), (true, vertices_166), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_644), (true, vertices_200), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 17 12 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_23) then 10 else
  if p.val = (false, vertices_583) then 18 else
  if p.val = (false, vertices_51) then 11 else
  if p.val = (false, vertices_803) then 21 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_841) then 13 else
  if p.val = (false, vertices_369) then 16 else
  if p.val = (true, vertices_166) then 19 else
  if p.val = (true, vertices_76) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_23), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 6 7 5 472 392 1
cert_row_4 1 1 6 7 8 2 908 644 2
cert_row_4 2 4 6 7 8 3 944 672 2
cert_row_2 3 1 4 6 0 166
cert_rows
cert_pivot_2 5 2 3 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 3 0 1 3 4 22 182 3
cert_coverFacet 1 678
cert_cover_5 1 3 0 1 4 8 166 678 3
cert_coverFacet 2 204
cert_cover_2 2 2 1 5 6 76 204 3
cert_coverFacet 3 588
cert_cover_2 3 2 1 5 8 76 588 3
cert_coverFacet 4 908
cert_cover_5 4 1 1 2 6 7 140 908 3
cert_coverFacet 5 472
cert_cover_5 5 0 2 3 5 6 200 472 1
cert_coverFacet 6 944
cert_cover_5 6 2 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_177

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_178.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_178

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 405, 805, 709, 233, 417, 790, 346, 362, 722, 802, 660, 440, 216, 133, 261, 517, 97, 161, 289, 545, 193, 577, 385, 330, 82, 274, 530, 98, 290, 546, 578, 770, 148, 276, 532, 644, 772, 88, 152, 280, 104, 168, 296, 200, 208, 400, 656, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_405, vertices_805, vertices_709, vertices_233, vertices_417, vertices_790, vertices_346, vertices_362, vertices_722, vertices_802, vertices_660, vertices_440, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_330, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_208, vertices_400, vertices_656, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_405), (false, vertices_805), (false, vertices_709), (false, vertices_233), (false, vertices_417), (true, vertices_330), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_532), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_417) then 12 else
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
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 82 274 530 290 770 532 88 152 280 296 208 656 417 611 330 405 805 709 233
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 7 8 1 790 274 3
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 2 4 6 7 3 440 168 3
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
cert_coverFacet 6 440
cert_cover_5 6 2 2 3 4 6 152 440 2
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_178

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P0_179.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_179

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 213, 677, 837, 809, 353, 342, 410, 426, 210, 354, 796, 660, 696, 69, 133, 517, 97, 161, 289, 545, 193, 321, 769, 394, 82, 146, 274, 98, 162, 290, 194, 322, 84, 148, 276, 532, 324, 644, 772, 152, 280, 536, 168, 296, 552, 776, 208, 656, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_213, vertices_677, vertices_837, vertices_809, vertices_353, vertices_342, vertices_410, vertices_426, vertices_210, vertices_354, vertices_796, vertices_660, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_769, vertices_394, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_644, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_776, vertices_208, vertices_656, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_213), (false, vertices_677), (false, vertices_837), (false, vertices_809), (false, vertices_353), (true, vertices_394), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_322), (true, vertices_276), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_353) then 12 else
  if p.val = (true, vertices_394) then 15 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 82 146 274 290 322 276 532 152 280 536 168 656 353 227 394 213 677 837 809
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 5 342 274 1
cert_row_4 1 2 3 7 8 1 796 280 3
cert_row_4 2 2 4 6 8 3 696 168 3
cert_row_2 3 2 6 7 0 394
cert_rows
cert_pivot_2 5 1 3 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 82 342 1
cert_coverFacet 1 410
cert_cover_5 1 3 0 2 3 6 394 410 2
cert_coverFacet 2 426
cert_cover_5 2 3 0 2 4 6 394 426 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 796
cert_cover_5 5 1 1 2 3 7 276 796 1
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 696
cert_cover_5 7 2 2 3 4 6 152 696 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_179

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P0_180.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_180

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 837, 601, 241, 817, 449, 654, 806, 454, 570, 170, 716, 184, 216, 49, 81, 529, 161, 289, 193, 321, 577, 385, 769, 134, 262, 518, 42, 138, 522, 162, 290, 546, 386, 652, 196, 324, 580, 772, 56, 88, 152, 536, 168, 200, 584, 176, 560, 208, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_837, vertices_601, vertices_241, vertices_817, vertices_449, vertices_654, vertices_806, vertices_454, vertices_570, vertices_170, vertices_716, vertices_184, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_529, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_652, vertices_196, vertices_324, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_200, vertices_584, vertices_176, vertices_560, vertices_208, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_837), (false, vertices_601), (false, vertices_241), (false, vertices_817), (false, vertices_449), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_546), (true, vertices_652), (true, vertices_196), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_449) then 12 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_652) then 17 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_200) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 5 454 134 3
cert_row_4 1 0 1 4 8 7 806 518 2
cert_row_4 2 2 3 4 8 0 570 56 3
cert_row_2 3 2 6 8 1 652
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 3 0 1 2 6 134 654 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 262 806 2
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 6 134 454 2
cert_coverFacet 3 570
cert_cover_5 3 2 0 2 3 4 42 570 2
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 652 716 2
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_180

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/P0_182.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_182

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 837, 809, 713, 241, 353, 782, 406, 710, 298, 650, 434, 372, 212, 41, 137, 521, 97, 161, 289, 193, 321, 577, 769, 134, 262, 518, 42, 138, 266, 522, 402, 162, 290, 642, 84, 148, 276, 196, 324, 580, 772, 296, 648, 776, 112, 176, 304, 208, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_837, vertices_809, vertices_713, vertices_241, vertices_353, vertices_782, vertices_406, vertices_710, vertices_298, vertices_650, vertices_434, vertices_372, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_522, vertices_402, vertices_162, vertices_290, vertices_642, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_580, vertices_772, vertices_296, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_837), (false, vertices_809), (false, vertices_713), (false, vertices_241), (false, vertices_353), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_402), (true, vertices_290), (true, vertices_642), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_353) then 12 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_402) then 15 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_304) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 134 262 518 266 522 290 642 84 148 276 196 304 353 171 402 837 809 713 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 2 782 262 3
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_4 2 3 4 5 7 1 372 112 3
cert_row_2 3 3 6 7 0 402
cert_rows
cert_pivot_2 2 8 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 406
cert_cover_5 1 3 0 1 3 6 134 406 2
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 134 710 2
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 434
cert_cover_5 5 3 0 3 4 6 402 434 2
cert_coverFacet 6 372
cert_cover_5 6 2 1 3 4 5 84 372 2
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_182

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/P0_183.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_183

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 805, 217, 369, 689, 833, 398, 678, 838, 458, 316, 172, 184, 344, 49, 81, 145, 289, 545, 193, 321, 577, 641, 769, 134, 262, 518, 394, 194, 322, 578, 642, 44, 140, 268, 164, 292, 548, 772, 56, 88, 152, 280, 168, 200, 328, 176, 304, 336, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_805, vertices_217, vertices_369, vertices_689, vertices_833, vertices_398, vertices_678, vertices_838, vertices_458, vertices_316, vertices_172, vertices_184, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_145, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_134, vertices_262, vertices_518, vertices_394, vertices_194, vertices_322, vertices_578, vertices_642, vertices_44, vertices_140, vertices_268, vertices_164, vertices_292, vertices_548, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_200, vertices_328, vertices_176, vertices_304, vertices_336, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_805), (false, vertices_217), (false, vertices_369), (false, vertices_689), (false, vertices_833), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_394), (true, vertices_322), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_833) then 12 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_394) then 15 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_328) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 5 838 262 3
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 2 3 4 7 1 316 56 3
cert_row_2 3 2 6 7 0 394
cert_rows
cert_pivot_2 5 8 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 134 398 2
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 134 678 2
cert_coverFacet 2 838
cert_cover_5 2 0 0 1 5 7 262 838 2
cert_coverFacet 3 458
cert_cover_5 3 3 0 2 5 6 394 458 2
cert_coverFacet 4 316
cert_cover_5 4 2 1 2 3 4 44 316 2
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_183

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/P0_185.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_185

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 789, 409, 681, 841, 342, 534, 230, 678, 458, 402, 620, 836, 232, 137, 265, 521, 145, 273, 529, 641, 769, 22, 166, 70, 518, 146, 274, 530, 194, 322, 386, 642, 276, 532, 100, 548, 324, 580, 772, 104, 168, 552, 200, 328, 584, 392, 400, 224, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_789, vertices_409, vertices_681, vertices_841, vertices_342, vertices_534, vertices_230, vertices_678, vertices_458, vertices_402, vertices_620, vertices_836, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_22, vertices_166, vertices_70, vertices_518, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_400, vertices_224, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_789), (false, vertices_409), (false, vertices_681), (false, vertices_841), (true, vertices_22), (true, vertices_166), (true, vertices_70), (true, vertices_518), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_100), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_104), (true, vertices_200), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_166) then 16 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 0 0 1 5 7 3 342 70 3
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 1 4 5 8 2 620 100 3
cert_row_2 3 1 4 6 0 166
cert_rows
cert_pivot_2 3 7 2 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 230
cert_cover_5 2 3 0 1 4 5 166 230 3
cert_coverFacet 3 678
cert_cover_5 3 3 0 1 4 8 166 678 3
cert_coverFacet 4 458
cert_cover_5 4 1 0 2 5 6 194 458 1
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 620
cert_cover_5 6 2 1 2 4 5 100 620 1
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_185

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2103 : Certifies 2103 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_145.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2104 : Certifies 2104 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_146.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2105 : Certifies 2105 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_147.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2106 : Certifies 2106 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_149.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2107 : Certifies 2107 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_151.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2108 : Certifies 2108 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_152.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2109 : Certifies 2109 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_153.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2110 : Certifies 2110 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_154.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2111 : Certifies 2111 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_155.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2112 : Certifies 2112 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_156.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2113 : Certifies 2113 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_157.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2114 : Certifies 2114 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_158.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2115 : Certifies 2115 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_159.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2116 : Certifies 2116 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_162.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2117 : Certifies 2117 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_165.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2118 : Certifies 2118 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_166.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2119 : Certifies 2119 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_170.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2120 : Certifies 2120 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_171.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2121 : Certifies 2121 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_172.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2122 : Certifies 2122 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_173.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2123 : Certifies 2123 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_174.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2124 : Certifies 2124 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_175.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2125 : Certifies 2125 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_176.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2126 : Certifies 2126 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_177.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2127 : Certifies 2127 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_178.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2128 : Certifies 2128 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_179.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2129 : Certifies 2129 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_180.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2130 : Certifies 2130 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_182.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2131 : Certifies 2131 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_183.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2132 : Certifies 2132 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_185.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B069 (j : Fin 30) :
    Certifies (2103 + j.val) := by
  fin_cases j
  · exact projection_2103
  · exact projection_2104
  · exact projection_2105
  · exact projection_2106
  · exact projection_2107
  · exact projection_2108
  · exact projection_2109
  · exact projection_2110
  · exact projection_2111
  · exact projection_2112
  · exact projection_2113
  · exact projection_2114
  · exact projection_2115
  · exact projection_2116
  · exact projection_2117
  · exact projection_2118
  · exact projection_2119
  · exact projection_2120
  · exact projection_2121
  · exact projection_2122
  · exact projection_2123
  · exact projection_2124
  · exact projection_2125
  · exact projection_2126
  · exact projection_2127
  · exact projection_2128
  · exact projection_2129
  · exact projection_2130
  · exact projection_2131
  · exact projection_2132

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
