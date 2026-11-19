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
/- Source: ProjectionCertificates/P0_312.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_312

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 613, 361, 681, 465, 705, 302, 558, 342, 534, 666, 402, 724, 356, 41, 137, 265, 97, 545, 193, 321, 577, 385, 641, 46, 22, 262, 518, 138, 266, 522, 146, 274, 530, 386, 84, 532, 100, 292, 548, 324, 580, 296, 552, 648, 208, 336, 400, 656, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_613, vertices_361, vertices_681, vertices_465, vertices_705, vertices_302, vertices_558, vertices_342, vertices_534, vertices_666, vertices_402, vertices_724, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_46, vertices_22, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_84, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_296, vertices_552, vertices_648, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_613), (false, vertices_361), (false, vertices_681), (false, vertices_465), (false, vertices_705), (true, vertices_46), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_84), (true, vertices_532), (true, vertices_292), (true, vertices_324), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_705) then 12 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_656) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 22 262 518 522 146 274 530 84 532 292 324 656 705 395 46 613 361 681 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 1 3 6 8 5 724 532 2
cert_row_4 2 0 2 6 8 3 666 138 3
cert_row_2 3 1 2 4 0 46
cert_rows
cert_pivot_2 7 5 3 0
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 3 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 3 0 1 2 8 46 558 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 5 22 342 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 666
cert_cover_5 4 2 0 2 3 6 138 666 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 724
cert_cover_5 6 1 1 3 5 6 84 724 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_312

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_313.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_313

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 421, 837, 361, 721, 225, 782, 390, 314, 602, 434, 658, 248, 840, 133, 261, 517, 97, 161, 289, 193, 321, 577, 641, 134, 262, 518, 26, 266, 522, 306, 146, 530, 386, 642, 388, 772, 56, 88, 104, 296, 328, 584, 776, 176, 208, 592, 656, 224, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_421, vertices_837, vertices_361, vertices_721, vertices_225, vertices_782, vertices_390, vertices_314, vertices_602, vertices_434, vertices_658, vertices_248, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_306, vertices_146, vertices_530, vertices_386, vertices_642, vertices_388, vertices_772, vertices_56, vertices_88, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_224, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_421), (false, vertices_837), (false, vertices_361), (false, vertices_721), (false, vertices_225), (true, vertices_262), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_306), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_56), (true, vertices_88), (true, vertices_584), (true, vertices_776), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_225) then 12 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_306) then 15 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_176) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_306), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 7 8 1 782 266 3
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_4 2 3 4 5 6 2 248 176 2
cert_row_2 3 3 4 7 0 306
cert_rows
cert_pivot_2 1 8 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 314
cert_cover_5 2 3 0 2 3 4 26 314 3
cert_coverFacet 3 602
cert_cover_5 3 1 0 2 3 5 26 602 3
cert_coverFacet 4 434
cert_cover_5 4 3 0 3 4 6 306 434 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 56 248 3
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_313

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_314.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_314

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 405, 677, 837, 569, 177, 454, 122, 538, 842, 242, 402, 708, 744, 133, 261, 517, 49, 145, 273, 529, 161, 545, 769, 26, 74, 522, 114, 146, 274, 530, 194, 322, 386, 770, 196, 324, 580, 388, 644, 56, 536, 104, 552, 584, 176, 400, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_405, vertices_677, vertices_837, vertices_569, vertices_177, vertices_454, vertices_122, vertices_538, vertices_842, vertices_242, vertices_402, vertices_708, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_769, vertices_26, vertices_74, vertices_522, vertices_114, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_770, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_536, vertices_104, vertices_552, vertices_584, vertices_176, vertices_400, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_405), (false, vertices_677), (false, vertices_837), (false, vertices_569), (false, vertices_177), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_114), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_196), (true, vertices_104), (true, vertices_584), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_177) then 12 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_114) then 15 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 26 74 522 146 194 322 386 196 104 584 224 704 177 787 114 405 677 837 569
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 1 454 194 3
cert_row_4 1 0 2 5 8 7 842 74 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 3 4 5 0 114
cert_rows
cert_pivot_2 1 7 2 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
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
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 744
cert_cover_5 7 2 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_314

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_316.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_316

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 155, 275, 163, 789, 613, 689, 794, 458, 482, 844, 356, 664, 744, 19, 35, 131, 259, 37, 261, 517, 145, 273, 529, 161, 545, 26, 138, 266, 274, 162, 290, 450, 100, 292, 324, 580, 772, 152, 536, 200, 328, 584, 648, 776, 656, 784, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_155, vertices_275, vertices_163, vertices_789, vertices_613, vertices_689, vertices_794, vertices_458, vertices_482, vertices_844, vertices_356, vertices_664, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_259, vertices_37, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_26, vertices_138, vertices_266, vertices_274, vertices_162, vertices_290, vertices_450, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_656, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_155), (false, vertices_275), (false, vertices_163), (false, vertices_789), (false, vertices_613), (false, vertices_689), (true, vertices_266), (true, vertices_450), (true, vertices_324), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_155) then 17 else
  if p.val = (false, vertices_275) then 10 else
  if p.val = (false, vertices_163) then 11 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_450) then 18 else
  if p.val = (true, vertices_324) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_200) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
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
cert_row_4 0 0 2 7 8 3 794 266 3
cert_row_4 1 2 5 7 8 1 844 328 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 5 6 7 0 450
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 26 794 3
cert_coverFacet 1 458
cert_cover_5 1 3 0 2 5 6 138 458 2
cert_coverFacet 2 482
cert_cover_5 2 3 0 4 5 6 162 482 2
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 324 844 1
cert_coverFacet 4 356
cert_cover_2 4 4 1 5 7 100 356 3
cert_coverFacet 5 664
cert_cover_2 5 3 2 6 8 152 664 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 200 744 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_316

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_317.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_317

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 555, 339, 99, 405, 533, 625, 426, 778, 482, 908, 724, 744, 464, 35, 67, 259, 515, 21, 261, 517, 81, 273, 529, 97, 545, 42, 266, 522, 98, 418, 322, 770, 148, 532, 388, 644, 772, 168, 552, 392, 648, 776, 208, 336, 592, 400, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_555, vertices_339, vertices_99, vertices_405, vertices_533, vertices_625, vertices_426, vertices_778, vertices_482, vertices_908, vertices_724, vertices_744, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_21, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_42, vertices_266, vertices_522, vertices_98, vertices_418, vertices_322, vertices_770, vertices_148, vertices_532, vertices_388, vertices_644, vertices_772, vertices_168, vertices_552, vertices_392, vertices_648, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_555), (false, vertices_339), (false, vertices_99), (false, vertices_405), (false, vertices_533), (false, vertices_625), (true, vertices_266), (true, vertices_418), (true, vertices_644), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_208), (true, vertices_224), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 15 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_99) then 10 else
  if p.val = (false, vertices_405) then 14 else
  if p.val = (false, vertices_533) then 11 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_418) then 19 else
  if p.val = (true, vertices_644) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_392) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_418), by decide +kernel⟩
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
cert_row_4 0 1 5 6 8 3 724 644 1
cert_row_4 1 2 6 7 8 1 908 392 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 4 6 7 0 418
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 3 0 2 4 6 42 426 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 482
cert_cover_5 2 3 0 4 5 6 98 482 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 388 908 1
cert_coverFacet 4 724
cert_cover_5 4 0 1 3 5 6 148 724 2
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 168 744 2
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_317

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_318.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_318

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 301, 405, 677, 617, 393, 662, 458, 586, 626, 466, 308, 564, 376, 37, 133, 261, 41, 137, 265, 521, 545, 385, 641, 74, 138, 522, 82, 146, 530, 450, 578, 642, 52, 148, 276, 532, 292, 548, 644, 104, 296, 328, 584, 392, 112, 304, 560, 336, 400, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_301, vertices_405, vertices_677, vertices_617, vertices_393, vertices_662, vertices_458, vertices_586, vertices_626, vertices_466, vertices_308, vertices_564, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_41, vertices_137, vertices_265, vertices_521, vertices_545, vertices_385, vertices_641, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_450, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_548, vertices_644, vertices_104, vertices_296, vertices_328, vertices_584, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_400, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_301), (false, vertices_405), (false, vertices_677), (false, vertices_617), (false, vertices_393), (true, vertices_74), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_450), (true, vertices_578), (true, vertices_52), (true, vertices_532), (true, vertices_328), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_393) then 12 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_450) then 15 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 74 82 146 530 578 52 532 328 112 304 560 336 393 651 450 301 405 677 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 8 1 662 146 3
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 3 4 5 7 2 376 112 3
cert_row_2 3 5 6 7 0 450
cert_rows
cert_pivot_2 1 8 2 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 458
cert_cover_5 1 3 0 2 5 6 74 458 3
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 626
cert_cover_5 3 1 0 3 4 5 82 626 2
cert_coverFacet 4 466
cert_cover_5 4 3 0 3 5 6 82 466 3
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 376
cert_cover_5 7 2 2 3 4 5 104 376 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_318

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_319.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_319

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 805, 793, 625, 465, 417, 110, 782, 422, 218, 394, 620, 600, 408, 81, 273, 529, 97, 161, 289, 545, 193, 385, 769, 14, 38, 262, 74, 138, 266, 98, 162, 194, 386, 108, 524, 292, 548, 772, 88, 152, 280, 536, 584, 392, 776, 208, 592, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_805, vertices_793, vertices_625, vertices_465, vertices_417, vertices_110, vertices_782, vertices_422, vertices_218, vertices_394, vertices_620, vertices_600, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_14, vertices_38, vertices_262, vertices_74, vertices_138, vertices_266, vertices_98, vertices_162, vertices_194, vertices_386, vertices_108, vertices_524, vertices_292, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_584, vertices_392, vertices_776, vertices_208, vertices_592, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_805), (false, vertices_793), (false, vertices_625), (false, vertices_465), (false, vertices_417), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_108), (true, vertices_524), (true, vertices_88), (true, vertices_152), (true, vertices_584), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 14 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_417) then 12 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_392) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 14 3
cert_row_4 1 0 1 4 6 7 422 38 3
cert_row_4 2 2 3 5 6 0 218 88 3
cert_row_2 3 2 4 5 1 108
cert_rows
cert_pivot_2 8 7 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 3 0 1 2 4 14 110 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 7 14 782 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 38 422 3
cert_coverFacet 3 218
cert_cover_5 3 2 0 2 3 5 74 218 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 8 108 620 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_319

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_320.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_320

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 837, 121, 665, 457, 593, 110, 334, 806, 170, 394, 690, 628, 184, 25, 73, 137, 81, 529, 321, 577, 385, 641, 769, 78, 38, 262, 42, 138, 266, 162, 546, 386, 642, 770, 100, 548, 324, 580, 772, 56, 152, 104, 168, 328, 392, 112, 176, 560, 592, 656]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_837, vertices_121, vertices_665, vertices_457, vertices_593, vertices_110, vertices_334, vertices_806, vertices_170, vertices_394, vertices_690, vertices_628, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_81, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_38, vertices_262, vertices_42, vertices_138, vertices_266, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_104, vertices_168, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_592, vertices_656] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_837), (false, vertices_121), (false, vertices_665), (false, vertices_457), (false, vertices_593), (true, vertices_78), (true, vertices_38), (true, vertices_262), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_162), (true, vertices_546), (true, vertices_100), (true, vertices_548), (true, vertices_168), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_593) then 12 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_4 0 0 1 4 8 7 806 38 3
cert_row_4 1 0 3 4 8 6 690 546 1
cert_row_4 2 1 4 5 8 3 628 100 3
cert_row_2 3 1 2 5 0 78
cert_rows
cert_pivot_2 7 6 3 0
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 3 0 1 2 4 78 110 3
cert_coverFacet 1 334
cert_cover_5 1 3 0 1 2 7 78 334 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 38 806 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 690
cert_cover_5 5 1 0 3 4 6 162 690 1
cert_coverFacet 6 628
cert_cover_5 6 2 1 3 4 5 100 628 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_320

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_321.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_321

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 403, 835, 589, 233, 449, 790, 658, 572, 364, 436, 836, 696, 480, 131, 259, 515, 73, 137, 521, 193, 321, 577, 385, 146, 274, 530, 642, 770, 44, 76, 524, 52, 276, 532, 292, 324, 580, 772, 568, 104, 168, 648, 176, 400, 656, 224, 352, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_403, vertices_835, vertices_589, vertices_233, vertices_449, vertices_790, vertices_658, vertices_572, vertices_364, vertices_436, vertices_836, vertices_696, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_193, vertices_321, vertices_577, vertices_385, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_44, vertices_76, vertices_524, vertices_52, vertices_276, vertices_532, vertices_292, vertices_324, vertices_580, vertices_772, vertices_568, vertices_104, vertices_168, vertices_648, vertices_176, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_403), (false, vertices_835), (false, vertices_589), (false, vertices_233), (false, vertices_449), (true, vertices_530), (true, vertices_44), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_568), (true, vertices_176), (true, vertices_656), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_449) then 12 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_568) then 21 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_568), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 7 8 0 790 276 3
cert_row_4 1 1 2 4 7 5 364 44 3
cert_row_4 2 3 4 6 7 1 436 176 3
cert_row_2 3 3 4 8 2 568
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 572
cert_cover_5 2 3 1 2 3 4 44 572 2
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 44 364 3
cert_coverFacet 4 436
cert_cover_5 4 2 1 3 4 6 52 436 3
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 568 696 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_321

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_322.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_322

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 283, 147, 163, 789, 613, 689, 666, 458, 482, 844, 356, 792, 744, 19, 35, 131, 259, 37, 261, 517, 145, 273, 529, 161, 545, 26, 138, 266, 146, 162, 290, 450, 100, 292, 324, 580, 772, 280, 536, 200, 328, 584, 648, 776, 656, 784, 224, 352, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_283, vertices_147, vertices_163, vertices_789, vertices_613, vertices_689, vertices_666, vertices_458, vertices_482, vertices_844, vertices_356, vertices_792, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_259, vertices_37, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_26, vertices_138, vertices_266, vertices_146, vertices_162, vertices_290, vertices_450, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_656, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_283), (false, vertices_147), (false, vertices_163), (false, vertices_789), (false, vertices_613), (false, vertices_689), (true, vertices_138), (true, vertices_450), (true, vertices_324), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_283) then 17 else
  if p.val = (false, vertices_147) then 10 else
  if p.val = (false, vertices_163) then 11 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_450) then 18 else
  if p.val = (true, vertices_324) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_200) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
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
cert_row_4 0 0 2 6 8 3 666 138 3
cert_row_4 1 2 5 7 8 1 844 328 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 5 6 7 0 450
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 0 0 2 3 6 26 666 3
cert_coverFacet 1 458
cert_cover_5 1 3 0 2 5 6 138 458 2
cert_coverFacet 2 482
cert_cover_5 2 3 0 4 5 6 162 482 2
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 324 844 1
cert_coverFacet 4 356
cert_cover_2 4 4 1 5 7 100 356 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 200 744 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_322

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_323.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_323

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 613, 793, 681, 393, 481, 598, 150, 358, 422, 410, 786, 668, 676, 137, 265, 521, 97, 161, 545, 321, 577, 385, 769, 22, 294, 70, 134, 146, 274, 530, 322, 578, 386, 770, 148, 532, 100, 164, 548, 580, 644, 152, 280, 536, 392, 648, 784, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_613, vertices_793, vertices_681, vertices_393, vertices_481, vertices_598, vertices_150, vertices_358, vertices_422, vertices_410, vertices_786, vertices_668, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_294, vertices_70, vertices_134, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_386, vertices_770, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_392, vertices_648, vertices_784, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_613), (false, vertices_793), (false, vertices_681), (false, vertices_393), (false, vertices_481), (true, vertices_22), (true, vertices_294), (true, vertices_70), (true, vertices_134), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_152)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_393) then 12 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_294) then 15 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_152) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 0 0 1 3 8 5 598 22 3
cert_row_4 1 1 2 3 6 8 668 148 1
cert_row_4 2 0 3 6 7 2 410 146 3
cert_row_2 3 1 4 7 0 294
cert_rows
cert_pivot_2 5 8 2 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 358
cert_cover_5 2 3 0 1 4 5 294 358 3
cert_coverFacet 3 422
cert_cover_5 3 3 0 1 4 6 294 422 3
cert_coverFacet 4 410
cert_cover_5 4 2 0 2 3 6 146 410 1
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 668
cert_cover_5 6 1 1 2 3 6 148 668 1
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_323

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_324.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_324

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 309, 149, 185, 617, 801, 214, 342, 646, 714, 866, 232, 496, 21, 133, 261, 517, 41, 137, 521, 49, 145, 289, 545, 769, 86, 134, 262, 518, 194, 322, 578, 642, 770, 148, 276, 644, 104, 168, 200, 584, 648, 176, 304, 208, 336, 224, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_309, vertices_149, vertices_185, vertices_617, vertices_801, vertices_214, vertices_342, vertices_646, vertices_714, vertices_866, vertices_232, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_521, vertices_49, vertices_145, vertices_289, vertices_545, vertices_769, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_148, vertices_276, vertices_644, vertices_104, vertices_168, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_309), (false, vertices_149), (false, vertices_185), (false, vertices_617), (false, vertices_801), (true, vertices_86), (true, vertices_134), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_200), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_149) then 10 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_801) then 11 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
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
cert_row_4 0 0 5 6 8 2 714 194 3
cert_row_4 1 0 4 5 7 8 866 322 1
cert_row_4 2 3 5 6 7 4 496 208 3
cert_row_2 3 1 3 5 0 86
cert_rows
cert_pivot_2 2 8 4 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 3 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 3 0 1 3 7 86 342 3
cert_coverFacet 2 646
cert_cover_2 2 1 0 6 8 134 646 3
cert_coverFacet 3 714
cert_cover_5 3 0 0 2 5 6 194 714 1
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 322 866 1
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 496
cert_cover_5 6 2 3 4 5 6 176 496 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_324

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_325.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_325

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 157, 269, 805, 121, 297, 689, 398, 838, 458, 722, 216, 872, 624, 13, 133, 261, 517, 25, 41, 265, 49, 145, 289, 545, 641, 134, 262, 518, 394, 194, 322, 578, 642, 140, 268, 772, 88, 152, 104, 296, 200, 328, 112, 560, 208, 592, 656, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_157, vertices_269, vertices_805, vertices_121, vertices_297, vertices_689, vertices_398, vertices_838, vertices_458, vertices_722, vertices_216, vertices_872, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_134, vertices_262, vertices_518, vertices_394, vertices_194, vertices_322, vertices_578, vertices_642, vertices_140, vertices_268, vertices_772, vertices_88, vertices_152, vertices_104, vertices_296, vertices_200, vertices_328, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_157), (false, vertices_269), (false, vertices_805), (false, vertices_121), (false, vertices_297), (false, vertices_689), (true, vertices_262), (true, vertices_394), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_200), (true, vertices_328), (true, vertices_208), (true, vertices_592), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_269) then 10 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_297) then 11 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_394) then 14 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 262 1 194 2 322 578 200 328 208 592 608 832 269 297 647 394 157 805 121 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 7 8 1 838 322 3
cert_row_4 1 0 5 6 8 3 722 194 3
cert_row_4 2 2 5 7 8 4 872 328 3
cert_row_2 3 2 6 7 0 394
cert_rows
cert_pivot_2 1 3 4 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 134 398 2
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 262 838 2
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 394 458 2
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 194 722 1
cert_coverFacet 4 216
cert_cover_2 4 3 2 5 6 88 216 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_325

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_326.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_326

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 205, 405, 837, 425, 777, 598, 570, 234, 242, 212, 788, 808, 944, 69, 133, 261, 73, 137, 265, 521, 577, 385, 769, 42, 74, 522, 50, 82, 530, 226, 578, 84, 148, 276, 532, 196, 580, 772, 168, 296, 552, 200, 776, 176, 560, 208, 400, 784, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_205, vertices_405, vertices_837, vertices_425, vertices_777, vertices_598, vertices_570, vertices_234, vertices_242, vertices_212, vertices_788, vertices_808, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_73, vertices_137, vertices_265, vertices_521, vertices_577, vertices_385, vertices_769, vertices_42, vertices_74, vertices_522, vertices_50, vertices_82, vertices_530, vertices_226, vertices_578, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_772, vertices_168, vertices_296, vertices_552, vertices_200, vertices_776, vertices_176, vertices_560, vertices_208, vertices_400, vertices_784, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_205), (false, vertices_405), (false, vertices_837), (false, vertices_425), (false, vertices_777), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_226), (true, vertices_84), (true, vertices_532), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_777) then 12 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_226) then 15 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 42 50 82 530 84 532 552 176 560 208 784 800 777 587 226 205 405 837 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 8 1 598 82 3
cert_row_4 1 0 3 4 8 2 570 50 3
cert_row_4 2 4 6 7 8 3 944 416 3
cert_row_2 3 4 5 6 0 226
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 42 570 2
cert_coverFacet 2 234
cert_cover_5 2 3 0 2 4 5 42 234 3
cert_coverFacet 3 242
cert_cover_5 3 3 0 3 4 5 50 242 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 944
cert_cover_5 7 2 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_326

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_327.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_327

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 397, 789, 677, 625, 417, 782, 602, 458, 114, 786, 482, 652, 744, 133, 261, 517, 49, 273, 529, 161, 289, 545, 385, 74, 266, 522, 50, 82, 274, 530, 98, 290, 450, 770, 140, 268, 524, 644, 772, 200, 584, 392, 648, 112, 592, 784, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_397, vertices_789, vertices_677, vertices_625, vertices_417, vertices_782, vertices_602, vertices_458, vertices_114, vertices_786, vertices_482, vertices_652, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_450, vertices_770, vertices_140, vertices_268, vertices_524, vertices_644, vertices_772, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_397), (false, vertices_789), (false, vertices_677), (false, vertices_625), (false, vertices_417), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_450), (true, vertices_770), (true, vertices_524), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_417) then 12 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_450) then 15 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 7 8 1 782 266 3
cert_row_4 1 0 2 5 8 3 602 74 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 5 6 7 0 450
cert_rows
cert_pivot_2 1 3 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 74 602 2
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 74 458 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 482
cert_cover_5 5 3 0 4 5 6 98 482 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 744
cert_cover_5 7 2 2 4 5 6 200 744 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_327

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_328.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_328

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 661, 421, 773, 841, 465, 678, 314, 346, 618, 178, 658, 812, 432, 133, 261, 517, 81, 145, 529, 321, 577, 385, 769, 282, 42, 74, 50, 82, 146, 530, 162, 546, 578, 642, 164, 292, 548, 644, 772, 296, 552, 328, 584, 776, 176, 304, 336, 400, 656, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_661, vertices_421, vertices_773, vertices_841, vertices_465, vertices_678, vertices_314, vertices_346, vertices_618, vertices_178, vertices_658, vertices_812, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_769, vertices_282, vertices_42, vertices_74, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_546, vertices_578, vertices_642, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_656, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_661), (false, vertices_421), (false, vertices_773), (false, vertices_841), (false, vertices_465), (true, vertices_282), (true, vertices_42), (true, vertices_74), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_773) then 12 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_282) then 15 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
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
cert_row_4 0 0 1 4 8 6 678 546 1
cert_row_4 1 0 2 4 8 5 618 42 3
cert_row_4 2 2 4 7 8 1 812 296 3
cert_row_2 3 2 3 7 0 282
cert_rows
cert_pivot_2 6 5 1 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 314
cert_cover_5 1 3 0 2 3 4 282 314 3
cert_coverFacet 2 346
cert_cover_5 2 3 0 2 3 5 282 346 3
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 5 42 618 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 812
cert_cover_5 6 2 1 2 4 7 292 812 1
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_328

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_329.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_329

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 805, 453, 681, 705, 342, 186, 794, 810, 210, 450, 788, 728, 69, 261, 517, 161, 289, 545, 193, 577, 385, 641, 26, 42, 778, 82, 146, 274, 162, 290, 194, 322, 386, 84, 276, 532, 324, 772, 152, 536, 168, 552, 648, 208, 592, 784, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_805, vertices_453, vertices_681, vertices_705, vertices_342, vertices_186, vertices_794, vertices_810, vertices_210, vertices_450, vertices_788, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_778, vertices_82, vertices_146, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_84, vertices_276, vertices_532, vertices_324, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_648, vertices_208, vertices_592, vertices_784, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_805), (false, vertices_453), (false, vertices_681), (false, vertices_705), (true, vertices_26), (true, vertices_42), (true, vertices_778), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_276), (true, vertices_152), (true, vertices_536), (true, vertices_208), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_705) then 12 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_778) then 15 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 26 42 82 146 274 194 322 276 152 536 208 784 705 419 778 597 805 453 681
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 1 342 82 3
cert_row_4 1 0 2 3 6 4 186 26 3
cert_row_4 2 2 5 6 8 3 728 648 1
cert_row_2 3 2 7 8 0 778
cert_rows
cert_pivot_2 1 4 3 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 82 342 1
cert_coverFacet 1 186
cert_cover_5 1 1 0 2 3 4 26 186 3
cert_coverFacet 2 794
cert_cover_5 2 3 0 2 3 7 26 794 3
cert_coverFacet 3 810
cert_cover_5 3 3 0 2 4 7 42 810 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 728
cert_cover_5 7 2 2 3 5 6 152 728 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_329

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_330.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_330

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 555, 339, 99, 661, 277, 625, 426, 778, 482, 908, 468, 744, 720, 35, 67, 259, 515, 21, 261, 517, 81, 273, 529, 97, 545, 42, 266, 522, 98, 418, 322, 770, 148, 276, 388, 644, 772, 168, 552, 392, 648, 776, 208, 336, 592, 656, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_555, vertices_339, vertices_99, vertices_661, vertices_277, vertices_625, vertices_426, vertices_778, vertices_482, vertices_908, vertices_468, vertices_744, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_21, vertices_261, vertices_517, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_42, vertices_266, vertices_522, vertices_98, vertices_418, vertices_322, vertices_770, vertices_148, vertices_276, vertices_388, vertices_644, vertices_772, vertices_168, vertices_552, vertices_392, vertices_648, vertices_776, vertices_208, vertices_336, vertices_592, vertices_656, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_555), (false, vertices_339), (false, vertices_99), (false, vertices_661), (false, vertices_277), (false, vertices_625), (true, vertices_266), (true, vertices_418), (true, vertices_388), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_208), (true, vertices_224), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 15 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_99) then 10 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_277) then 11 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_418) then 19 else
  if p.val = (true, vertices_388) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_392) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_418), by decide +kernel⟩
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
cert_row_4 0 1 5 6 7 3 468 388 1
cert_row_4 1 2 6 7 8 1 908 392 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 4 6 7 0 418
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 3 0 2 4 6 42 426 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 482
cert_cover_5 2 3 0 4 5 6 98 482 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 388 908 1
cert_coverFacet 4 468
cert_cover_5 4 0 1 3 5 6 148 468 2
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 168 744 2
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_330

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_331.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_331

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 837, 409, 681, 777, 481, 598, 150, 358, 422, 666, 674, 796, 404, 137, 265, 521, 97, 161, 545, 321, 577, 385, 769, 22, 294, 70, 134, 146, 530, 98, 162, 546, 578, 642, 148, 276, 532, 324, 580, 388, 772, 152, 280, 536, 648, 776, 400, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_837, vertices_409, vertices_681, vertices_777, vertices_481, vertices_598, vertices_150, vertices_358, vertices_422, vertices_666, vertices_674, vertices_796, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_294, vertices_70, vertices_134, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_388, vertices_772, vertices_152, vertices_280, vertices_536, vertices_648, vertices_776, vertices_400, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_837), (false, vertices_409), (false, vertices_681), (false, vertices_777), (false, vertices_481), (true, vertices_22), (true, vertices_294), (true, vertices_70), (true, vertices_134), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_536)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_777) then 12 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_294) then 15 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_536) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 0 0 1 3 8 5 598 22 3
cert_row_4 1 0 2 3 8 6 666 530 1
cert_row_4 2 1 3 7 8 2 796 276 3
cert_row_2 3 1 4 7 0 294
cert_rows
cert_pivot_2 5 6 2 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 358
cert_cover_5 2 3 0 1 4 5 294 358 3
cert_coverFacet 3 422
cert_cover_5 3 3 0 1 4 6 294 422 3
cert_coverFacet 4 666
cert_cover_5 4 1 0 2 3 6 146 666 1
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 796
cert_cover_5 6 2 1 2 3 7 276 796 1
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_331

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_332.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_332

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 653, 789, 421, 625, 673, 782, 602, 458, 114, 786, 482, 396, 744, 133, 261, 517, 49, 273, 529, 161, 289, 545, 641, 74, 266, 522, 50, 82, 274, 530, 98, 290, 450, 770, 140, 268, 524, 388, 772, 200, 584, 392, 648, 112, 592, 784, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_653, vertices_789, vertices_421, vertices_625, vertices_673, vertices_782, vertices_602, vertices_458, vertices_114, vertices_786, vertices_482, vertices_396, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_450, vertices_770, vertices_140, vertices_268, vertices_524, vertices_388, vertices_772, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_653), (false, vertices_789), (false, vertices_421), (false, vertices_625), (false, vertices_673), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_450), (true, vertices_770), (true, vertices_268), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_673) then 12 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_450) then 15 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 7 8 1 782 266 3
cert_row_4 1 0 2 5 8 3 602 74 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 5 6 7 0 450
cert_rows
cert_pivot_2 1 3 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 74 602 2
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 74 458 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 482
cert_cover_5 5 3 0 4 5 6 98 482 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 744
cert_cover_5 7 2 2 4 5 6 200 744 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_332

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_333.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_333

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 661, 389, 105, 713, 481, 790, 618, 778, 242, 306, 722, 436, 133, 261, 517, 41, 73, 265, 521, 97, 289, 193, 385, 641, 42, 266, 522, 50, 210, 274, 530, 98, 290, 578, 770, 148, 276, 532, 388, 772, 104, 584, 776, 176, 304, 656, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_661, vertices_389, vertices_105, vertices_713, vertices_481, vertices_790, vertices_618, vertices_778, vertices_242, vertices_306, vertices_722, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_385, vertices_641, vertices_42, vertices_266, vertices_522, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_290, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_104, vertices_584, vertices_776, vertices_176, vertices_304, vertices_656, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_661), (false, vertices_389), (false, vertices_105), (false, vertices_713), (false, vertices_481), (true, vertices_522), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_578), (true, vertices_770), (true, vertices_276), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_389) then 10 else
  if p.val = (false, vertices_105) then 11 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_210) then 14 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 8 2 618 98 3
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 3 4 6 7 1 436 176 3
cert_row_2 3 3 5 6 0 210
cert_rows
cert_pivot_2 2 8 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 618
cert_cover_5 1 0 0 2 4 5 42 618 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 242
cert_cover_5 3 3 0 3 4 5 50 242 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 722
cert_cover_5 5 3 0 3 5 8 210 722 3
cert_coverFacet 6 436
cert_cover_5 6 2 1 3 4 6 148 436 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_333

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_334.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_334

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 837, 617, 425, 369, 897, 342, 534, 902, 186, 570, 402, 628, 432, 41, 137, 521, 97, 289, 321, 577, 385, 641, 769, 22, 262, 518, 58, 138, 522, 146, 274, 530, 386, 642, 84, 532, 324, 580, 772, 168, 552, 112, 176, 304, 560, 336, 400, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_837, vertices_617, vertices_425, vertices_369, vertices_897, vertices_342, vertices_534, vertices_902, vertices_186, vertices_570, vertices_402, vertices_628, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_262, vertices_518, vertices_58, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_168, vertices_552, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_400, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_837), (false, vertices_617), (false, vertices_425), (false, vertices_369), (false, vertices_897), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_58), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_84), (true, vertices_532), (true, vertices_176), (true, vertices_560), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_897) then 12 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_58) then 15 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 22 262 518 146 274 530 386 84 532 176 560 400 897 651 58 837 617 425 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 6 902 262 3
cert_row_4 1 0 1 3 5 7 342 22 3
cert_row_4 2 3 4 5 8 1 628 112 3
cert_row_2 3 2 3 4 0 58
cert_rows
cert_pivot_2 6 7 1 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 22 342 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 902
cert_cover_5 2 0 0 1 6 7 262 902 2
cert_coverFacet 3 186
cert_cover_5 3 3 0 2 3 6 58 186 3
cert_coverFacet 4 570
cert_cover_5 4 3 0 2 3 8 58 570 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 628
cert_cover_5 6 2 1 3 4 5 84 628 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_334

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_335.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_335

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 307, 547, 557, 77, 181, 213, 345, 678, 418, 962, 844, 708, 496, 35, 259, 515, 13, 149, 37, 69, 73, 265, 521, 49, 81, 273, 545, 162, 290, 546, 386, 642, 770, 76, 524, 164, 548, 196, 580, 644, 328, 776, 176, 304, 208, 336, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_307, vertices_547, vertices_557, vertices_77, vertices_181, vertices_213, vertices_345, vertices_678, vertices_418, vertices_962, vertices_844, vertices_708, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_13, vertices_149, vertices_37, vertices_69, vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_273, vertices_545, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_328, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_307), (false, vertices_547), (false, vertices_557), (false, vertices_77), (false, vertices_181), (false, vertices_213), (false, vertices_345), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_580), (true, vertices_644), (true, vertices_416), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_307) then 13 else
  if p.val = (false, vertices_547) then 9 else
  if p.val = (false, vertices_557) then 15 else
  if p.val = (false, vertices_77) then 10 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (true, vertices_162) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 5 7 8 2 844 580 2
cert_row_4 1 0 4 6 8 1 678 162 3
cert_row_4 2 5 6 7 8 0 962 448 3
cert_row_4 3 4 5 6 7 3 496 416 1
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 418
cert_cover_2 1 4 0 6 7 162 418 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 386 962 1
cert_coverFacet 3 844
cert_cover_5 3 0 1 2 5 7 76 844 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 176 496 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_335

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_336.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_336

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 675, 291, 653, 313, 153, 241, 838, 370, 610, 220, 348, 780, 740, 35, 259, 515, 25, 137, 265, 521, 49, 145, 161, 289, 641, 98, 290, 546, 322, 578, 770, 92, 140, 268, 524, 196, 324, 580, 644, 772, 152, 280, 776, 112, 304, 208, 336, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_675, vertices_291, vertices_653, vertices_313, vertices_153, vertices_241, vertices_838, vertices_370, vertices_610, vertices_220, vertices_348, vertices_780, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_161, vertices_289, vertices_641, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_92, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_280, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_675), (false, vertices_291), (false, vertices_653), (false, vertices_313), (false, vertices_153), (false, vertices_241), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_92), (true, vertices_268), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_336), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_291) then 10 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_313) then 19 else
  if p.val = (false, vertices_153) then 11 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_92) then 17 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 5 8 6 740 580 1
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 3 4 5 7 0 370 112 3
cert_row_2 3 2 3 5 1 92
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 370
cert_cover_5 1 2 0 3 4 5 98 370 1
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 220
cert_cover_5 3 3 1 2 3 6 92 220 3
cert_coverFacet 4 348
cert_cover_5 4 3 1 2 3 7 92 348 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 740
cert_cover_5 6 0 1 4 5 6 196 740 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_336

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_337.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_337

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 391, 587, 643, 345, 665, 433, 614, 166, 690, 844, 820, 420, 792, 263, 67, 131, 515, 25, 73, 521, 145, 273, 321, 385, 641, 38, 70, 134, 162, 546, 578, 642, 164, 292, 548, 324, 580, 388, 772, 280, 536, 328, 584, 776, 176, 304, 560, 656, 784, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_391, vertices_587, vertices_643, vertices_345, vertices_665, vertices_433, vertices_614, vertices_166, vertices_690, vertices_844, vertices_820, vertices_420, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_67, vertices_131, vertices_515, vertices_25, vertices_73, vertices_521, vertices_145, vertices_273, vertices_321, vertices_385, vertices_641, vertices_38, vertices_70, vertices_134, vertices_162, vertices_546, vertices_578, vertices_642, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_772, vertices_280, vertices_536, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_560, vertices_656, vertices_784, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_391), (false, vertices_587), (false, vertices_643), (false, vertices_345), (false, vertices_665), (false, vertices_433), (true, vertices_38), (true, vertices_162), (true, vertices_546), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_772), (true, vertices_776), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_643) then 11 else
  if p.val = (false, vertices_345) then 18 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 8 6 690 546 1
cert_row_4 1 1 4 5 8 0 614 548 2
cert_row_4 2 1 5 7 8 2 844 324 3
cert_row_4 3 3 4 7 8 1 820 304 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 38 614 3
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 690
cert_cover_5 2 0 0 3 4 6 162 690 1
cert_coverFacet 3 844
cert_cover_5 3 2 1 2 5 7 324 844 1
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 292 820 1
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_337

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P1_001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [31, 555, 339, 803, 205, 85, 361, 526, 662, 914, 684, 468, 232, 992, 11, 19, 547, 259, 13, 21, 69, 41, 73, 81, 289, 321, 14, 22, 518, 522, 658, 274, 770, 140, 524, 84, 148, 196, 644, 104, 168, 552, 200, 336, 400, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_31, vertices_555, vertices_339, vertices_803, vertices_205, vertices_85, vertices_361, vertices_526, vertices_662, vertices_914, vertices_684, vertices_468, vertices_232, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_547, vertices_259, vertices_13, vertices_21, vertices_69, vertices_41, vertices_73, vertices_81, vertices_289, vertices_321, vertices_14, vertices_22, vertices_518, vertices_522, vertices_658, vertices_274, vertices_770, vertices_140, vertices_524, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_168, vertices_552, vertices_200, vertices_336, vertices_400, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_31), (false, vertices_555), (false, vertices_339), (false, vertices_803), (false, vertices_205), (false, vertices_85), (false, vertices_361), (true, vertices_518), (true, vertices_658), (true, vertices_524), (true, vertices_148), (true, vertices_644), (true, vertices_168), (true, vertices_400), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 11 14 16 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_31) then 12 else
  if p.val = (false, vertices_555) then 20 else
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_803) then 21 else
  if p.val = (false, vertices_205) then 13 else
  if p.val = (false, vertices_85) then 10 else
  if p.val = (false, vertices_361) then 15 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_658) then 18 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_31), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_658), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 6 8 2 684 644 1
cert_row_4 1 3 5 6 7 1 468 336 2
cert_row_4 2 5 6 7 8 4 992 448 3
cert_row_2 3 3 6 8 0 658
cert_rows
cert_pivot_2 2 1 4 0
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 662
cert_cover_5 1 3 0 1 3 6 22 662 3
cert_coverFacet 2 914
cert_cover_5 2 3 0 3 6 7 658 914 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 140 684 2
cert_coverFacet 4 468
cert_cover_5 4 1 1 3 5 6 84 468 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_001

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P1_003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 789, 809, 433, 721, 214, 406, 358, 618, 418, 706, 604, 364, 780, 145, 273, 529, 161, 289, 545, 641, 769, 150, 70, 262, 98, 162, 290, 546, 194, 578, 386, 642, 76, 268, 524, 84, 276, 532, 356, 772, 104, 296, 552, 584, 776, 208, 592, 400, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_789, vertices_809, vertices_433, vertices_721, vertices_214, vertices_406, vertices_358, vertices_618, vertices_418, vertices_706, vertices_604, vertices_364, vertices_780] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_150, vertices_70, vertices_262, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_578, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_356, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_208, vertices_592, vertices_400, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_789), (false, vertices_809), (false, vertices_433), (false, vertices_721), (true, vertices_150), (true, vertices_70), (true, vertices_262), (true, vertices_98), (true, vertices_290), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_356), (true, vertices_104), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_150) then 15 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_356) then 18 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 2 5 8 4 618 578 1
cert_row_4 2 1 3 5 8 2 604 84 3
cert_row_2 3 1 3 6 0 150
cert_rows
cert_pivot_2 7 4 2 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 3 0 1 3 5 150 214 3
cert_coverFacet 1 406
cert_cover_5 1 3 0 1 3 7 150 406 3
cert_coverFacet 2 358
cert_cover_5 2 0 0 1 4 5 70 358 2
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 5 98 618 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 604
cert_cover_5 6 2 1 2 3 5 76 604 2
cert_coverFacet 7 364
cert_cover_5 7 0 1 2 4 5 76 364 2
cert_coverFacet 8 780
cert_cover_2 8 2 1 7 8 268 780 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_003

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m13e10q1_0145.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0145

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 775, 661, 229, 793, 465, 102, 550, 810, 482, 684, 440, 664, 263, 69, 133, 517, 145, 273, 529, 193, 321, 769, 38, 70, 518, 98, 290, 546, 322, 770, 100, 164, 548, 644, 152, 280, 536, 168, 296, 552, 648, 776, 400, 656, 224, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_775, vertices_661, vertices_229, vertices_793, vertices_465, vertices_102, vertices_550, vertices_810, vertices_482, vertices_684, vertices_440, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_69, vertices_133, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_769, vertices_38, vertices_70, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_100, vertices_164, vertices_548, vertices_644, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_400, vertices_656, vertices_224, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_775), (false, vertices_661), (false, vertices_229), (false, vertices_793), (false, vertices_465), (true, vertices_38), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_548), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_648), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_661) then 15 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 98 3
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 1 2 4 6 8 684 164 1
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 102
cert_cover_2 0 1 0 4 5 38 102 3
cert_coverFacet 1 550
cert_cover_2 1 1 0 4 8 38 550 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 290 810 1
cert_coverFacet 3 482
cert_cover_5 3 0 0 4 5 6 98 482 3
cert_coverFacet 4 684
cert_cover_5 4 2 1 2 4 6 164 684 1
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 152 440 2
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0145

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 781, 229, 421, 313, 617, 214, 390, 774, 794, 626, 402, 568, 496, 165, 69, 261, 517, 41, 265, 521, 97, 289, 577, 70, 134, 262, 518, 82, 146, 274, 530, 578, 386, 770, 196, 388, 772, 56, 280, 536, 552, 776, 112, 304, 560, 208, 400, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_781, vertices_229, vertices_421, vertices_313, vertices_617, vertices_214, vertices_390, vertices_774, vertices_794, vertices_626, vertices_402, vertices_568, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_165, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_97, vertices_289, vertices_577, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_578, vertices_386, vertices_770, vertices_196, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_781), (false, vertices_229), (false, vertices_421), (false, vertices_313), (false, vertices_617), (true, vertices_134), (true, vertices_262), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_536), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 134 1 262 2 82 146 274 530 386 770 536 112 560 208 400 583 781 229 421 313 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 70 2
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 70 214 2
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 794
cert_cover_5 3 1 0 2 3 7 274 794 1
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 82 626 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0001

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 781, 613, 453, 121, 345, 902, 410, 170, 778, 738, 708, 184, 496, 69, 261, 517, 89, 41, 265, 521, 97, 545, 321, 42, 138, 266, 522, 162, 546, 386, 642, 770, 196, 580, 388, 644, 772, 56, 152, 280, 168, 776, 112, 176, 336, 400, 224, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_781, vertices_613, vertices_453, vertices_121, vertices_345, vertices_902, vertices_410, vertices_170, vertices_778, vertices_738, vertices_708, vertices_184, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_89, vertices_41, vertices_265, vertices_521, vertices_97, vertices_545, vertices_321, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_781), (false, vertices_613), (false, vertices_453), (false, vertices_121), (false, vertices_345), (true, vertices_138), (true, vertices_266), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
cert_nodeAtPriority 0 138 1 266 2 162 386 642 770 644 152 168 176 400 224 704 555 781 613 453 121 345
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 138 410 2
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0002

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2223 : Certifies 2223 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_312.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2224 : Certifies 2224 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_313.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2225 : Certifies 2225 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_314.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2226 : Certifies 2226 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_316.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2227 : Certifies 2227 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_317.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2228 : Certifies 2228 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_318.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2229 : Certifies 2229 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_319.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2230 : Certifies 2230 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_320.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2231 : Certifies 2231 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_321.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2232 : Certifies 2232 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_322.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2233 : Certifies 2233 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_323.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2234 : Certifies 2234 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_324.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2235 : Certifies 2235 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_325.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2236 : Certifies 2236 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_326.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2237 : Certifies 2237 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_327.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2238 : Certifies 2238 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_328.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2239 : Certifies 2239 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_329.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2240 : Certifies 2240 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_330.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2241 : Certifies 2241 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_331.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2242 : Certifies 2242 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_332.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2243 : Certifies 2243 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_333.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2244 : Certifies 2244 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_334.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2245 : Certifies 2245 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_335.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2246 : Certifies 2246 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_336.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2247 : Certifies 2247 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_337.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2248 : Certifies 2248 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2249 : Certifies 2249 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P1_003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2250 : Certifies 2250 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m13e10q1_0145.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2251 : Certifies 2251 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2252 : Certifies 2252 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B073 (j : Fin 30) :
    Certifies (2223 + j.val) := by
  fin_cases j
  · exact projection_2223
  · exact projection_2224
  · exact projection_2225
  · exact projection_2226
  · exact projection_2227
  · exact projection_2228
  · exact projection_2229
  · exact projection_2230
  · exact projection_2231
  · exact projection_2232
  · exact projection_2233
  · exact projection_2234
  · exact projection_2235
  · exact projection_2236
  · exact projection_2237
  · exact projection_2238
  · exact projection_2239
  · exact projection_2240
  · exact projection_2241
  · exact projection_2242
  · exact projection_2243
  · exact projection_2244
  · exact projection_2245
  · exact projection_2246
  · exact projection_2247
  · exact projection_2248
  · exact projection_2249
  · exact projection_2250
  · exact projection_2251
  · exact projection_2252

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
