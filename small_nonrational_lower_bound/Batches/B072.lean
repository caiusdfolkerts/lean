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
/- Source: ProjectionCertificates/P0_278.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_278

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 789, 409, 689, 481, 838, 234, 682, 586, 354, 604, 284, 460, 664, 145, 273, 529, 161, 289, 545, 385, 769, 170, 74, 522, 98, 290, 546, 322, 578, 770, 28, 76, 268, 276, 532, 324, 580, 772, 152, 280, 536, 200, 584, 392, 648, 656, 224, 352, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_789, vertices_409, vertices_689, vertices_481, vertices_838, vertices_234, vertices_682, vertices_586, vertices_354, vertices_604, vertices_284, vertices_460, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_769, vertices_170, vertices_74, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_76, vertices_268, vertices_276, vertices_532, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_392, vertices_648, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_789), (false, vertices_409), (false, vertices_689), (false, vertices_481), (true, vertices_170), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_580), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_170) then 16 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 1 2 5 8 3 604 76 3
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 2 5 6 7 1 460 200 3
cert_row_2 3 2 4 6 0 170
cert_rows
cert_pivot_2 3 8 1 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 234
cert_cover_5 1 3 0 2 4 5 170 234 3
cert_coverFacet 2 682
cert_cover_5 2 3 0 2 4 8 170 682 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 604
cert_cover_5 5 0 1 2 3 5 28 604 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 460
cert_cover_5 7 2 1 2 5 6 76 460 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_278

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_279.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_279

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 139, 675, 653, 793, 625, 305, 398, 454, 370, 226, 844, 740, 848, 11, 35, 131, 137, 265, 521, 49, 273, 529, 289, 545, 641, 390, 138, 266, 98, 162, 290, 194, 322, 140, 268, 524, 196, 324, 580, 644, 776, 112, 304, 336, 592, 784, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_139, vertices_675, vertices_653, vertices_793, vertices_625, vertices_305, vertices_398, vertices_454, vertices_370, vertices_226, vertices_844, vertices_740, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_131, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_289, vertices_545, vertices_641, vertices_390, vertices_138, vertices_266, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_644, vertices_776, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_139), (false, vertices_675), (false, vertices_653), (false, vertices_793), (false, vertices_625), (false, vertices_305), (true, vertices_390), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_268), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_336), (true, vertices_224), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_139) then 10 else
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_305) then 11 else
  if p.val = (true, vertices_390) then 14 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 1 98 0 194 2 322 268 196 324 580 336 224 832 139 305 653 390 299 675 793 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 7 3 370 98 3
cert_row_4 1 1 5 7 8 2 844 324 3
cert_row_4 2 1 5 6 8 4 740 196 3
cert_row_2 3 1 6 7 0 390
cert_rows
cert_pivot_2 3 2 4 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 390 398 2
cert_coverFacet 1 454
cert_cover_5 1 3 0 1 5 6 390 454 2
cert_coverFacet 2 370
cert_cover_5 2 0 0 3 4 5 98 370 1
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 844
cert_cover_5 4 1 1 2 5 7 268 844 2
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 196 740 1
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_279

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_280.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_280

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 355, 195, 771, 805, 217, 625, 902, 458, 668, 364, 620, 396, 600, 67, 131, 259, 515, 81, 145, 529, 97, 289, 545, 193, 769, 194, 322, 386, 642, 770, 108, 140, 268, 524, 292, 548, 388, 644, 772, 88, 152, 536, 200, 328, 584, 392, 592, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_355, vertices_195, vertices_771, vertices_805, vertices_217, vertices_625, vertices_902, vertices_458, vertices_668, vertices_364, vertices_620, vertices_396, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_769, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_108, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_592, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_355), (false, vertices_195), (false, vertices_771), (false, vertices_805), (false, vertices_217), (false, vertices_625), (true, vertices_386), (true, vertices_108), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_388), (true, vertices_644), (true, vertices_536), (true, vertices_328), (true, vertices_584), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_355) then 14 else
  if p.val = (false, vertices_195) then 10 else
  if p.val = (false, vertices_771) then 11 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_392) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 1 2 6 8 3 668 140 3
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 2 5 6 7 0 458 200 3
cert_row_2 3 2 4 5 1 108
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 458
cert_cover_5 1 2 0 2 5 6 194 458 1
cert_coverFacet 2 668
cert_cover_5 2 0 1 2 3 6 140 668 2
cert_coverFacet 3 364
cert_cover_5 3 3 1 2 4 7 108 364 3
cert_coverFacet 4 620
cert_cover_5 4 3 1 2 4 8 108 620 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_280

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_281.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_281

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 653, 269, 309, 613, 425, 225, 790, 906, 626, 466, 780, 564, 496, 13, 37, 261, 517, 137, 265, 97, 161, 289, 193, 577, 641, 82, 274, 530, 194, 578, 386, 642, 770, 268, 524, 52, 276, 532, 548, 772, 392, 648, 776, 112, 304, 560, 464, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_653, vertices_269, vertices_309, vertices_613, vertices_425, vertices_225, vertices_790, vertices_906, vertices_626, vertices_466, vertices_780, vertices_564, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_517, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_641, vertices_82, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_464, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_653), (false, vertices_269), (false, vertices_309), (false, vertices_613), (false, vertices_425), (false, vertices_225), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_772), (true, vertices_776), (true, vertices_112), (true, vertices_560), (true, vertices_464)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 13 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_269) then 10 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_225) then 11 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_464) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 3 7 8 1 790 274 3
cert_row_4 1 0 6 7 8 2 906 386 3
cert_row_4 2 3 4 5 8 0 626 112 3
cert_row_2 3 5 6 7 3 464
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 386 906 1
cert_coverFacet 2 626
cert_cover_5 2 2 0 3 4 5 82 626 2
cert_coverFacet 3 466
cert_cover_5 3 3 0 3 5 6 82 466 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_281

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_282.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_282

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 611, 419, 597, 121, 313, 902, 682, 348, 620, 396, 652, 788, 424, 35, 259, 515, 57, 81, 273, 529, 97, 289, 577, 162, 546, 386, 642, 770, 76, 140, 268, 524, 84, 276, 532, 580, 388, 644, 772, 88, 280, 104, 168, 296, 552, 392, 648, 784, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_611, vertices_419, vertices_597, vertices_121, vertices_313, vertices_902, vertices_682, vertices_348, vertices_620, vertices_396, vertices_652, vertices_788, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_57, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_784, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_611), (false, vertices_419), (false, vertices_597), (false, vertices_121), (false, vertices_313), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 7 3 348 76 3
cert_row_4 1 0 1 6 8 7 902 642 1
cert_row_4 2 2 4 6 8 0 682 168 3
cert_row_4 3 2 4 5 8 1 620 104 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 162 682 1
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 76 348 2
cert_coverFacet 3 620
cert_cover_5 3 3 1 2 4 5 76 620 2
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_282

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_283.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_283

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 595, 275, 589, 405, 645, 689, 618, 434, 562, 354, 684, 460, 488, 19, 67, 259, 69, 133, 261, 517, 145, 273, 529, 577, 641, 50, 274, 530, 98, 290, 546, 322, 578, 76, 140, 524, 324, 388, 644, 104, 168, 552, 456, 584, 176, 560, 400, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_595, vertices_275, vertices_589, vertices_405, vertices_645, vertices_689, vertices_618, vertices_434, vertices_562, vertices_354, vertices_684, vertices_460, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_69, vertices_133, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_577, vertices_641, vertices_50, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_76, vertices_140, vertices_524, vertices_324, vertices_388, vertices_644, vertices_104, vertices_168, vertices_552, vertices_456, vertices_584, vertices_176, vertices_560, vertices_400, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_595), (false, vertices_275), (false, vertices_589), (false, vertices_405), (false, vertices_645), (false, vertices_689), (true, vertices_50), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_140), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_456), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_275) then 10 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_645) then 11 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_456) then 19 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
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
cert_row_4 0 0 4 6 7 3 434 290 2
cert_row_4 1 2 4 5 8 0 618 104 3
cert_row_4 2 2 4 6 8 1 684 168 3
cert_row_2 3 5 6 7 2 456
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 618
cert_cover_5 0 1 0 2 4 5 98 618 1
cert_coverFacet 1 434
cert_cover_5 1 0 0 3 4 6 50 434 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 684
cert_cover_5 4 2 1 2 4 6 140 684 2
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 76 460 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_283

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_284.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_284

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 611, 291, 597, 313, 217, 233, 902, 426, 674, 412, 212, 788, 740, 35, 259, 515, 25, 41, 201, 81, 273, 529, 97, 289, 577, 162, 290, 546, 386, 642, 770, 84, 148, 276, 532, 196, 580, 388, 644, 772, 152, 280, 168, 296, 392, 208, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_611, vertices_291, vertices_597, vertices_313, vertices_217, vertices_233, vertices_902, vertices_426, vertices_674, vertices_412, vertices_212, vertices_788, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_25, vertices_41, vertices_201, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_208, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_611), (false, vertices_291), (false, vertices_597), (false, vertices_313), (false, vertices_217), (false, vertices_233), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_392), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 13 else
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_291) then 11 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_313) then 18 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (true, vertices_162) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 6 7 3 412 388 1
cert_row_4 1 0 4 6 7 2 426 162 3
cert_row_4 2 1 6 7 8 0 902 388 3
cert_row_4 3 4 5 6 8 1 740 224 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 162 426 1
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 148 412 1
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 196 740 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_284

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_286.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_286

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 587, 227, 541, 45, 425, 457, 674, 962, 316, 852, 932, 344, 600, 35, 67, 515, 13, 37, 517, 41, 73, 393, 521, 161, 193, 162, 546, 194, 578, 642, 28, 44, 276, 532, 292, 548, 772, 88, 280, 536, 296, 328, 584, 336, 592, 416, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_587, vertices_227, vertices_541, vertices_45, vertices_425, vertices_457, vertices_674, vertices_962, vertices_316, vertices_852, vertices_932, vertices_344, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_13, vertices_37, vertices_517, vertices_41, vertices_73, vertices_393, vertices_521, vertices_161, vertices_193, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_536, vertices_296, vertices_328, vertices_584, vertices_336, vertices_592, vertices_416, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_587), (false, vertices_227), (false, vertices_541), (false, vertices_45), (false, vertices_425), (false, vertices_457), (true, vertices_642), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_336), (true, vertices_592), (true, vertices_672), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_45) then 11 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 5 6 7 8 0 962 448 3
cert_row_4 1 1 3 4 7 2 316 276 2
cert_row_4 2 1 5 7 8 3 852 772 1
cert_row_4 3 4 6 7 8 1 932 416 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 674
cert_cover_2 0 4 0 6 8 162 674 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 316
cert_cover_5 2 1 1 2 3 4 28 316 3
cert_coverFacet 3 852
cert_cover_5 3 2 1 3 5 7 276 852 2
cert_coverFacet 4 932
cert_cover_5 4 3 1 4 6 7 292 932 2
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_286

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_287.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_287

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 781, 665, 425, 241, 865, 654, 182, 358, 838, 114, 658, 396, 420, 137, 265, 521, 81, 145, 529, 97, 161, 289, 577, 769, 38, 326, 134, 518, 50, 82, 146, 530, 98, 578, 642, 140, 268, 524, 164, 292, 388, 772, 392, 648, 112, 176, 656, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_781, vertices_665, vertices_425, vertices_241, vertices_865, vertices_654, vertices_182, vertices_358, vertices_838, vertices_114, vertices_658, vertices_396, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_289, vertices_577, vertices_769, vertices_38, vertices_326, vertices_134, vertices_518, vertices_50, vertices_82, vertices_146, vertices_530, vertices_98, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_388, vertices_772, vertices_392, vertices_648, vertices_112, vertices_176, vertices_656, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_781), (false, vertices_665), (false, vertices_425), (false, vertices_241), (false, vertices_865), (true, vertices_38), (true, vertices_326), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_98), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_292), (true, vertices_388)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 12 else
  if p.val = (false, vertices_781) then 15 else
  if p.val = (false, vertices_665) then 17 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_326) then 13 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_388) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 8 2 654 134 3
cert_row_4 1 0 1 4 6 3 182 38 3
cert_row_2 2 1 5 7 0 326
cert_rows_3
cert_pivot_3 3 2 0
cert_heightProof 3
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 182
cert_cover_5 1 1 0 1 3 4 38 182 2
cert_coverFacet 2 358
cert_cover_5 2 2 0 1 4 5 38 358 3
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 8 326 838 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_287

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_288.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_288

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 539, 355, 611, 345, 713, 534, 678, 294, 668, 436, 408, 456, 992, 19, 99, 259, 515, 25, 73, 521, 273, 321, 577, 22, 38, 262, 518, 530, 290, 546, 148, 276, 532, 164, 292, 644, 152, 280, 536, 200, 328, 392, 648, 400, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_539, vertices_355, vertices_611, vertices_345, vertices_713, vertices_534, vertices_678, vertices_294, vertices_668, vertices_436, vertices_408, vertices_456, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_99, vertices_259, vertices_515, vertices_25, vertices_73, vertices_521, vertices_273, vertices_321, vertices_577, vertices_22, vertices_38, vertices_262, vertices_518, vertices_530, vertices_290, vertices_546, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_644, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_539), (false, vertices_355), (false, vertices_611), (false, vertices_345), (false, vertices_713), (true, vertices_38), (true, vertices_518), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_644), (true, vertices_152), (true, vertices_392), (true, vertices_400), (true, vertices_416), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 13 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 14 else
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
cert_nodeAtPriority 1 38 0 518 2 148 532 164 292 644 152 392 400 416 672 448 279 539 355 611 345 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 6 8 0 678 164 3
cert_row_4 1 1 3 6 8 2 668 148 3
cert_row_4 2 3 4 6 7 1 436 400 1
cert_row_4 3 5 6 7 8 4 992 448 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 38 678 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 148 668 1
cert_coverFacet 4 436
cert_cover_5 4 2 1 3 4 6 148 436 2
cert_coverFacet 5 408
cert_cover_2 5 3 2 6 7 152 408 3
cert_coverFacet 6 456
cert_cover_2 6 5 2 6 7 200 456 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 352 992 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_288

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_289.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_289

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 391, 589, 565, 165, 345, 537, 433, 198, 842, 930, 706, 740, 824, 263, 37, 69, 133, 517, 25, 73, 521, 49, 273, 529, 161, 321, 385, 70, 134, 194, 322, 578, 386, 642, 770, 164, 548, 196, 580, 280, 536, 328, 584, 776, 304, 560, 416, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_391, vertices_589, vertices_565, vertices_165, vertices_345, vertices_537, vertices_433, vertices_198, vertices_842, vertices_930, vertices_706, vertices_740, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_37, vertices_69, vertices_133, vertices_517, vertices_25, vertices_73, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_321, vertices_385, vertices_70, vertices_134, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_164, vertices_548, vertices_196, vertices_580, vertices_280, vertices_536, vertices_328, vertices_584, vertices_776, vertices_304, vertices_560, vertices_416, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_391), (false, vertices_589), (false, vertices_565), (false, vertices_165), (false, vertices_345), (false, vertices_537), (false, vertices_433), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_196), (true, vertices_776), (true, vertices_672), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_565) then 16 else
  if p.val = (false, vertices_165) then 9 else
  if p.val = (false, vertices_345) then 18 else
  if p.val = (false, vertices_537) then 10 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (true, vertices_194) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 4 5 6 8 1 740 672 1
cert_row_4 1 0 2 7 8 5 842 770 1
cert_row_4 2 4 6 7 8 0 930 416 3
cert_row_4 3 3 4 7 8 2 824 304 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 198
cert_cover_2 0 1 0 5 6 70 198 3
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 930
cert_cover_5 2 2 0 4 6 7 386 930 1
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 740
cert_cover_5 4 0 1 4 5 6 164 740 2
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 280 824 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_289

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_290.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_290

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 397, 665, 841, 241, 449, 182, 662, 550, 114, 866, 812, 652, 484, 137, 265, 521, 81, 145, 529, 193, 321, 577, 385, 150, 38, 518, 50, 82, 530, 98, 546, 578, 140, 268, 524, 164, 292, 548, 388, 644, 648, 776, 112, 176, 656, 224, 352, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_397, vertices_665, vertices_841, vertices_241, vertices_449, vertices_182, vertices_662, vertices_550, vertices_114, vertices_866, vertices_812, vertices_652, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_150, vertices_38, vertices_518, vertices_50, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_648, vertices_776, vertices_112, vertices_176, vertices_656, vertices_224, vertices_352, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_397), (false, vertices_665), (false, vertices_841), (false, vertices_241), (false, vertices_449), (true, vertices_150), (true, vertices_38), (true, vertices_518), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_449) then 12 else
  if p.val = (true, vertices_150) then 15 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 38 518 50 98 546 524 164 292 548 644 352 800 449 595 150 397 665 841 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 7 8 2 812 292 3
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 1 5 6 7 4 484 388 1
cert_row_2 3 1 3 6 0 150
cert_rows
cert_pivot_2 2 8 4 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 3 0 1 3 4 150 182 3
cert_coverFacet 1 662
cert_cover_5 1 3 0 1 3 8 150 662 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 98 866 3
cert_coverFacet 5 812
cert_cover_5 5 0 1 2 4 7 268 812 2
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 484
cert_cover_5 7 2 1 4 5 6 164 484 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_290

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_291.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_291

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 837, 809, 713, 369, 225, 782, 406, 710, 298, 650, 434, 244, 340, 41, 137, 521, 97, 161, 289, 193, 321, 577, 769, 134, 262, 518, 42, 138, 266, 522, 402, 162, 290, 642, 84, 148, 276, 196, 324, 580, 772, 296, 648, 776, 112, 176, 304, 336, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_837, vertices_809, vertices_713, vertices_369, vertices_225, vertices_782, vertices_406, vertices_710, vertices_298, vertices_650, vertices_434, vertices_244, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_522, vertices_402, vertices_162, vertices_290, vertices_642, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_580, vertices_772, vertices_296, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_837), (false, vertices_809), (false, vertices_713), (false, vertices_369), (false, vertices_225), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_402), (true, vertices_290), (true, vertices_642), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_225) then 12 else
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
  if p.val = (true, vertices_176) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 134 262 518 266 522 290 642 84 148 276 196 176 225 171 402 837 809 713 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 2 782 262 3
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_4 2 3 4 5 6 1 244 112 3
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
cert_coverFacet 6 244
cert_cover_5 6 2 1 3 4 5 84 244 2
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_291

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_292.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_292

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 397, 309, 149, 713, 777, 689, 342, 842, 242, 306, 738, 220, 332, 21, 133, 261, 137, 265, 521, 49, 145, 289, 545, 641, 769, 50, 82, 274, 226, 290, 546, 322, 578, 770, 76, 140, 268, 84, 148, 276, 324, 200, 328, 584, 776, 176, 304, 208, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_397, vertices_309, vertices_149, vertices_713, vertices_777, vertices_689, vertices_342, vertices_842, vertices_242, vertices_306, vertices_738, vertices_220, vertices_332] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_769, vertices_50, vertices_82, vertices_274, vertices_226, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_324, vertices_200, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_397), (false, vertices_309), (false, vertices_149), (false, vertices_713), (false, vertices_777), (false, vertices_689), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_226), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_84), (true, vertices_324), (true, vertices_328), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_149) then 10 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_777) then 11 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_226) then 14 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_208) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 50 1 82 2 274 322 578 76 84 324 328 208 149 777 803 226 397 309 713 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_4 1 0 1 3 5 7 342 82 1
cert_row_4 2 2 3 5 6 1 220 200 1
cert_row_2 3 4 5 6 0 226
cert_rows
cert_pivot_2 8 7 1 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 82 342 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 322 842 1
cert_coverFacet 2 242
cert_cover_5 2 3 0 3 4 5 50 242 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 738
cert_cover_5 4 3 0 4 5 8 226 738 3
cert_coverFacet 5 220
cert_cover_5 5 2 1 2 3 5 76 220 2
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_292

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_293.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_293

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 339, 707, 653, 409, 241, 614, 370, 802, 812, 396, 436, 228, 708, 67, 259, 515, 137, 265, 521, 81, 145, 273, 193, 641, 338, 98, 290, 546, 578, 770, 140, 268, 524, 100, 164, 292, 548, 196, 580, 388, 644, 392, 776, 112, 176, 304, 400, 224, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_339, vertices_707, vertices_653, vertices_409, vertices_241, vertices_614, vertices_370, vertices_802, vertices_812, vertices_396, vertices_436, vertices_228, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_193, vertices_641, vertices_338, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_400, vertices_224, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_339), (false, vertices_707), (false, vertices_653), (false, vertices_409), (false, vertices_241), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_268), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_304), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 7 8 2 812 292 3
cert_row_4 1 0 1 4 5 8 614 98 1
cert_row_4 2 3 4 6 7 1 436 176 3
cert_row_2 3 3 5 7 0 338
cert_rows
cert_pivot_2 2 8 1 0
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 370
cert_cover_5 1 3 0 3 4 5 338 370 2
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 812
cert_cover_5 3 0 1 2 4 7 268 812 2
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 436
cert_cover_5 5 2 1 3 4 6 164 436 1
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_293

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_294.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_294

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 677, 837, 241, 369, 218, 538, 842, 690, 572, 780, 312, 344, 37, 261, 517, 113, 161, 289, 193, 321, 577, 641, 26, 74, 522, 146, 530, 194, 578, 642, 44, 268, 524, 548, 772, 56, 88, 280, 536, 296, 328, 776, 176, 304, 560, 208, 336, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_677, vertices_837, vertices_241, vertices_369, vertices_218, vertices_538, vertices_842, vertices_690, vertices_572, vertices_780, vertices_312, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_261, vertices_517, vertices_113, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_26, vertices_74, vertices_522, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_524, vertices_548, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_328, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_677), (false, vertices_837), (false, vertices_241), (false, vertices_369), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_524), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_776), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 8 7 842 74 3
cert_row_4 1 0 2 3 6 5 218 26 3
cert_row_4 2 3 4 6 8 0 690 176 3
cert_row_4 3 2 3 4 8 1 572 56 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 1 0 2 3 5 26 218 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 146 690 2
cert_coverFacet 4 572
cert_cover_5 4 3 1 2 3 4 44 572 2
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_294

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_295.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_295

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 307, 147, 613, 293, 689, 458, 778, 466, 844, 372, 744, 240, 19, 131, 259, 515, 37, 261, 517, 49, 145, 289, 545, 641, 138, 266, 522, 146, 274, 450, 770, 100, 292, 324, 580, 772, 200, 328, 584, 648, 776, 112, 176, 304, 208, 336, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_307, vertices_147, vertices_613, vertices_293, vertices_689, vertices_458, vertices_778, vertices_466, vertices_844, vertices_372, vertices_744, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_450, vertices_770, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_307), (false, vertices_147), (false, vertices_613), (false, vertices_293), (false, vertices_689), (true, vertices_266), (true, vertices_450), (true, vertices_324), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 15 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_147) then 10 else
  if p.val = (false, vertices_613) then 14 else
  if p.val = (false, vertices_293) then 11 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_450) then 19 else
  if p.val = (true, vertices_324) then 1 else
  if p.val = (true, vertices_200) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_224) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
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
cert_row_4 0 1 4 5 7 3 372 100 3
cert_row_4 1 2 5 7 8 1 844 328 3
cert_row_4 2 4 5 6 8 2 744 224 3
cert_row_2 3 5 6 7 0 450
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 458
cert_cover_5 0 3 0 2 5 6 138 458 2
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 466
cert_cover_5 2 3 0 3 5 6 146 466 2
cert_coverFacet 3 844
cert_cover_5 3 1 1 2 5 7 324 844 1
cert_coverFacet 4 372
cert_cover_5 4 0 1 3 4 5 100 372 1
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 200 744 1
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_295

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_297.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_297

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 397, 181, 613, 325, 169, 809, 214, 454, 906, 626, 658, 116, 696, 37, 69, 133, 261, 41, 137, 265, 161, 545, 321, 577, 769, 198, 82, 146, 530, 322, 578, 386, 642, 770, 52, 84, 148, 100, 324, 388, 168, 552, 392, 648, 776, 112, 176, 560, 656, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_397, vertices_181, vertices_613, vertices_325, vertices_169, vertices_809, vertices_214, vertices_454, vertices_906, vertices_626, vertices_658, vertices_116, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_261, vertices_41, vertices_137, vertices_265, vertices_161, vertices_545, vertices_321, vertices_577, vertices_769, vertices_198, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_100, vertices_324, vertices_388, vertices_168, vertices_552, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_560, vertices_656, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_397), (false, vertices_181), (false, vertices_613), (false, vertices_325), (false, vertices_169), (false, vertices_809), (true, vertices_198), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_84), (true, vertices_648), (true, vertices_112), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_397) then 16 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_325) then 10 else
  if p.val = (false, vertices_169) then 11 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (true, vertices_198) then 14 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_656) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 8 7 906 642 1
cert_row_4 1 3 4 6 8 2 696 176 3
cert_row_4 2 0 4 5 8 3 626 578 1
cert_row_2 3 1 5 6 0 198
cert_rows
cert_pivot_2 7 2 3 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 3 0 1 3 5 198 214 2
cert_coverFacet 1 454
cert_cover_5 1 3 0 1 5 7 198 454 3
cert_coverFacet 2 906
cert_cover_5 2 0 0 2 6 7 386 906 1
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 82 626 2
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 696
cert_cover_5 6 1 2 3 4 6 168 696 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_297

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_298.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_298

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 837, 185, 601, 457, 657, 110, 334, 806, 170, 394, 690, 628, 120, 25, 73, 137, 145, 529, 321, 577, 385, 641, 769, 78, 38, 262, 42, 138, 266, 162, 546, 386, 642, 770, 100, 548, 324, 580, 772, 56, 88, 104, 168, 328, 392, 112, 176, 560, 592, 656]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_837, vertices_185, vertices_601, vertices_457, vertices_657, vertices_110, vertices_334, vertices_806, vertices_170, vertices_394, vertices_690, vertices_628, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_38, vertices_262, vertices_42, vertices_138, vertices_266, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_88, vertices_104, vertices_168, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_592, vertices_656] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_837), (false, vertices_185), (false, vertices_601), (false, vertices_457), (false, vertices_657), (true, vertices_78), (true, vertices_38), (true, vertices_262), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_162), (true, vertices_546), (true, vertices_100), (true, vertices_548), (true, vertices_104), (true, vertices_112), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_657) then 12 else
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
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_112) then 10 else
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
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_298

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_301.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_301

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 157, 269, 309, 713, 777, 689, 342, 842, 242, 306, 738, 460, 212, 13, 21, 261, 137, 265, 521, 49, 145, 289, 545, 641, 769, 50, 82, 274, 226, 290, 546, 322, 578, 770, 140, 268, 84, 148, 276, 196, 324, 200, 328, 584, 776, 176, 304, 208, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_157, vertices_269, vertices_309, vertices_713, vertices_777, vertices_689, vertices_342, vertices_842, vertices_242, vertices_306, vertices_738, vertices_460, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_769, vertices_50, vertices_82, vertices_274, vertices_226, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_200, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_157), (false, vertices_269), (false, vertices_309), (false, vertices_713), (false, vertices_777), (false, vertices_689), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_226), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_328), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 13 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_269) then 10 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_777) then 11 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_226) then 14 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_208) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 50 1 82 2 274 322 578 84 196 324 328 208 269 777 803 226 157 309 713 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 3 342 322 1
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 2 5 6 7 1 460 200 3
cert_row_2 3 4 5 6 0 226
cert_rows
cert_pivot_2 3 8 1 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 82 342 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 242
cert_cover_5 2 3 0 3 4 5 50 242 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 738
cert_cover_5 4 3 0 4 5 8 226 738 3
cert_coverFacet 5 460
cert_cover_5 5 2 1 2 5 6 140 460 2
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_301

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_302.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_302

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 901, 601, 233, 649, 865, 118, 150, 358, 390, 186, 668, 852, 120, 73, 137, 521, 97, 161, 289, 577, 385, 641, 769, 22, 102, 134, 262, 50, 146, 162, 290, 386, 84, 148, 532, 324, 388, 644, 772, 56, 88, 152, 536, 104, 168, 648, 112, 592, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_901, vertices_601, vertices_233, vertices_649, vertices_865, vertices_118, vertices_150, vertices_358, vertices_390, vertices_186, vertices_668, vertices_852, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_102, vertices_134, vertices_262, vertices_50, vertices_146, vertices_162, vertices_290, vertices_386, vertices_84, vertices_148, vertices_532, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_648, vertices_112, vertices_592, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_901), (false, vertices_601), (false, vertices_233), (false, vertices_649), (false, vertices_865), (true, vertices_22), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_50), (true, vertices_146), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_324), (true, vertices_56), (true, vertices_152), (true, vertices_112)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_901) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_649) then 12 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_112) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 8 7 852 84 3
cert_row_4 1 1 2 3 6 8 668 148 1
cert_row_4 2 0 3 4 6 2 186 50 3
cert_row_2 3 1 4 5 0 102
cert_rows
cert_pivot_2 7 8 2 0
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 3 0 1 3 4 22 118 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 358
cert_cover_5 2 3 0 1 4 7 102 358 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 186
cert_cover_5 4 2 0 2 3 4 50 186 1
cert_coverFacet 5 668
cert_cover_5 5 1 1 2 3 6 148 668 1
cert_coverFacet 6 852
cert_cover_5 6 0 1 3 5 7 84 852 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_302

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_303.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_303

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 597, 405, 357, 713, 449, 310, 566, 362, 554, 906, 402, 620, 456, 21, 69, 261, 145, 529, 193, 321, 577, 385, 641, 54, 42, 266, 522, 146, 274, 530, 290, 546, 386, 642, 276, 532, 100, 292, 548, 580, 104, 552, 200, 328, 584, 392, 648, 400, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_597, vertices_405, vertices_357, vertices_713, vertices_449, vertices_310, vertices_566, vertices_362, vertices_554, vertices_906, vertices_402, vertices_620, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_42, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_104, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_400, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_597), (false, vertices_405), (false, vertices_357), (false, vertices_713), (false, vertices_449), (true, vertices_54), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_449) then 12 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 42 266 522 274 290 546 386 548 104 552 328 392 449 659 54 597 405 357 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 7 8 6 906 266 3
cert_row_4 1 0 2 4 5 7 362 42 3
cert_row_4 2 1 4 5 8 2 620 100 3
cert_row_2 3 1 3 4 0 54
cert_rows
cert_pivot_2 6 7 2 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 3 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 3 0 1 3 8 54 566 3
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 42 362 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 906
cert_cover_5 4 0 0 2 6 7 266 906 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 620
cert_cover_5 6 2 1 2 4 5 100 620 1
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_303

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_304.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_304

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 157, 301, 773, 57, 689, 865, 398, 838, 458, 722, 632, 216, 360, 13, 133, 261, 517, 25, 41, 49, 145, 289, 545, 641, 769, 134, 262, 518, 394, 194, 322, 578, 642, 140, 268, 772, 56, 88, 152, 104, 296, 200, 328, 560, 208, 592, 656, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_157, vertices_301, vertices_773, vertices_57, vertices_689, vertices_865, vertices_398, vertices_838, vertices_458, vertices_722, vertices_632, vertices_216, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_769, vertices_134, vertices_262, vertices_518, vertices_394, vertices_194, vertices_322, vertices_578, vertices_642, vertices_140, vertices_268, vertices_772, vertices_56, vertices_88, vertices_152, vertices_104, vertices_296, vertices_200, vertices_328, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_157), (false, vertices_301), (false, vertices_773), (false, vertices_57), (false, vertices_689), (false, vertices_865), (true, vertices_262), (true, vertices_394), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_88), (true, vertices_104), (true, vertices_200), (true, vertices_328), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_157) then 16 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_773) then 10 else
  if p.val = (false, vertices_57) then 11 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_394) then 14 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_592) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 7 8 1 838 322 3
cert_row_4 1 2 3 5 8 4 632 88 3
cert_row_4 2 0 5 6 8 3 722 194 3
cert_row_2 3 2 6 7 0 394
cert_rows
cert_pivot_2 1 4 3 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 134 398 2
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 262 838 2
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 394 458 2
cert_coverFacet 3 722
cert_cover_5 3 2 0 3 5 6 194 722 1
cert_coverFacet 4 632
cert_cover_5 4 1 2 3 4 5 56 632 3
cert_coverFacet 5 216
cert_cover_2 5 3 2 5 6 88 216 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_304

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_305.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_305

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 805, 217, 425, 841, 225, 214, 534, 230, 550, 602, 796, 436, 408, 73, 137, 265, 97, 161, 289, 545, 193, 577, 769, 22, 38, 198, 518, 82, 530, 98, 546, 578, 148, 276, 532, 164, 292, 548, 772, 88, 152, 280, 536, 584, 392, 776, 208, 400, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_805, vertices_217, vertices_425, vertices_841, vertices_225, vertices_214, vertices_534, vertices_230, vertices_550, vertices_602, vertices_796, vertices_436, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_22, vertices_38, vertices_198, vertices_518, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_584, vertices_392, vertices_776, vertices_208, vertices_400, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_805), (false, vertices_217), (false, vertices_425), (false, vertices_841), (false, vertices_225), (true, vertices_22), (true, vertices_38), (true, vertices_198), (true, vertices_518), (true, vertices_82), (true, vertices_530), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_280), (true, vertices_536), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_225) then 12 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_198) then 15 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 6 7 4 436 148 3
cert_row_4 1 1 2 3 8 7 796 532 1
cert_row_4 2 0 3 5 8 2 602 82 3
cert_row_2 3 1 5 6 0 198
cert_rows
cert_pivot_2 4 7 2 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 3 0 1 3 5 22 214 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 230
cert_cover_5 2 3 0 1 4 5 38 230 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 602
cert_cover_5 4 2 0 2 3 5 82 602 1
cert_coverFacet 5 796
cert_cover_5 5 1 1 2 3 7 276 796 1
cert_coverFacet 6 436
cert_cover_5 6 0 1 3 4 6 148 436 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_305

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_306.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_306

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 805, 361, 241, 849, 673, 398, 790, 678, 458, 210, 338, 236, 300, 81, 145, 529, 97, 161, 289, 545, 321, 641, 769, 134, 262, 518, 394, 82, 146, 274, 530, 194, 322, 642, 44, 140, 268, 164, 292, 548, 772, 104, 296, 200, 328, 208, 336, 784, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_805, vertices_361, vertices_241, vertices_849, vertices_673, vertices_398, vertices_790, vertices_678, vertices_458, vertices_210, vertices_338, vertices_236, vertices_300] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_641, vertices_769, vertices_134, vertices_262, vertices_518, vertices_394, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_642, vertices_44, vertices_140, vertices_268, vertices_164, vertices_292, vertices_548, vertices_772, vertices_104, vertices_296, vertices_200, vertices_328, vertices_208, vertices_336, vertices_784, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_805), (false, vertices_361), (false, vertices_241), (false, vertices_849), (false, vertices_673), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_394), (true, vertices_82), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (false, vertices_673) then 12 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_394) then 15 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_200) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 3 790 262 3
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 2 4 5 6 1 236 104 3
cert_row_2 3 2 6 7 0 394
cert_rows
cert_pivot_2 3 8 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 134 398 2
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 262 790 2
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 134 678 2
cert_coverFacet 3 458
cert_cover_5 3 3 0 2 5 6 394 458 2
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 236
cert_cover_5 6 2 1 2 4 5 44 236 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_306

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P0_307.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_307

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 405, 569, 217, 425, 785, 790, 230, 422, 582, 618, 604, 212, 232, 25, 41, 137, 145, 273, 529, 289, 545, 385, 769, 166, 70, 262, 518, 98, 290, 546, 578, 770, 84, 148, 276, 532, 196, 580, 388, 88, 536, 104, 168, 552, 200, 584, 208, 784, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_405, vertices_569, vertices_217, vertices_425, vertices_785, vertices_790, vertices_230, vertices_422, vertices_582, vertices_618, vertices_604, vertices_212, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_769, vertices_166, vertices_70, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_88, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_208, vertices_784, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_405), (false, vertices_569), (false, vertices_217), (false, vertices_425), (false, vertices_785), (true, vertices_166), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_578), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_104), (true, vertices_584), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_785) then 12 else
  if p.val = (true, vertices_166) then 15 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_166), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 8 7 790 518 2
cert_row_4 1 1 2 5 8 3 604 580 1
cert_row_4 2 0 4 5 8 2 618 98 3
cert_row_2 3 1 4 6 0 166
cert_rows
cert_pivot_2 7 3 2 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 262 790 2
cert_coverFacet 1 230
cert_cover_5 1 3 0 1 4 5 166 230 3
cert_coverFacet 2 422
cert_cover_5 2 3 0 1 4 7 166 422 3
cert_coverFacet 3 582
cert_cover_2 3 1 0 5 8 70 582 3
cert_coverFacet 4 618
cert_cover_5 4 2 0 2 4 5 98 618 1
cert_coverFacet 5 604
cert_cover_5 5 1 1 2 3 5 84 604 1
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_307

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P0_308.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_308

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 677, 185, 369, 721, 801, 398, 806, 710, 458, 316, 172, 216, 344, 49, 81, 145, 161, 289, 545, 321, 577, 641, 769, 134, 262, 518, 394, 194, 322, 578, 770, 44, 140, 268, 164, 292, 548, 644, 56, 88, 152, 280, 168, 200, 328, 304, 208, 336, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_677, vertices_185, vertices_369, vertices_721, vertices_801, vertices_398, vertices_806, vertices_710, vertices_458, vertices_316, vertices_172, vertices_216, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_145, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_134, vertices_262, vertices_518, vertices_394, vertices_194, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_268, vertices_164, vertices_292, vertices_548, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_200, vertices_328, vertices_304, vertices_208, vertices_336, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_677), (false, vertices_185), (false, vertices_369), (false, vertices_721), (false, vertices_801), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_394), (true, vertices_194), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_292), (true, vertices_88), (true, vertices_280), (true, vertices_200), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_801) then 12 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_394) then 15 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 8 5 710 134 3
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_4 2 2 3 4 7 1 316 56 3
cert_row_2 3 2 6 7 0 394
cert_rows
cert_pivot_2 5 8 1 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 134 398 2
cert_coverFacet 1 806
cert_cover_5 1 1 0 1 4 7 262 806 2
cert_coverFacet 2 710
cert_cover_5 2 0 0 1 5 6 134 710 2
cert_coverFacet 3 458
cert_cover_5 3 3 0 2 5 6 394 458 2
cert_coverFacet 4 316
cert_cover_5 4 2 1 2 3 4 44 316 2
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_308

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/P0_309.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_309

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 173, 805, 453, 569, 393, 838, 218, 538, 458, 626, 244, 612, 184, 37, 133, 261, 41, 137, 265, 521, 545, 385, 769, 26, 202, 266, 522, 82, 530, 322, 578, 770, 100, 164, 548, 196, 324, 580, 772, 56, 152, 536, 168, 392, 112, 176, 560, 208, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_173, vertices_805, vertices_453, vertices_569, vertices_393, vertices_838, vertices_218, vertices_538, vertices_458, vertices_626, vertices_244, vertices_612, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_41, vertices_137, vertices_265, vertices_521, vertices_545, vertices_385, vertices_769, vertices_26, vertices_202, vertices_266, vertices_522, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_173), (false, vertices_805), (false, vertices_453), (false, vertices_569), (false, vertices_393), (true, vertices_26), (true, vertices_202), (true, vertices_82), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_100), (true, vertices_580), (true, vertices_152), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_393) then 12 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_202) then 15 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 26 82 530 322 578 100 580 152 112 176 208 608 393 779 202 173 805 453 569
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 8 7 838 578 1
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 3 4 5 6 1 244 112 3
cert_row_2 3 2 5 6 0 202
cert_rows
cert_pivot_2 7 8 1 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 3 0 2 3 5 26 218 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 458
cert_cover_5 3 3 0 2 5 7 202 458 3
cert_coverFacet 4 626
cert_cover_5 4 1 0 3 4 5 82 626 2
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 100 244 1
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_309

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/P0_310.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_310

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 677, 345, 625, 433, 705, 558, 398, 710, 602, 330, 428, 312, 568, 49, 81, 273, 161, 545, 193, 321, 577, 385, 641, 14, 134, 518, 74, 266, 522, 194, 322, 578, 386, 44, 396, 164, 548, 644, 56, 88, 280, 536, 296, 552, 328, 304, 560, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_677, vertices_345, vertices_625, vertices_433, vertices_705, vertices_558, vertices_398, vertices_710, vertices_602, vertices_330, vertices_428, vertices_312, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_134, vertices_518, vertices_74, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_44, vertices_396, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_304, vertices_560, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_677), (false, vertices_345), (false, vertices_625), (false, vertices_433), (false, vertices_705), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_44), (true, vertices_396), (true, vertices_56), (true, vertices_536), (true, vertices_296), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_705) then 12 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 8 4 558 14 3
cert_row_4 1 0 2 5 8 3 602 74 3
cert_row_4 2 1 5 6 8 0 710 644 1
cert_row_2 3 2 6 7 1 396
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 14 558 3
cert_coverFacet 1 398
cert_cover_5 1 3 0 1 2 6 14 398 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 602
cert_cover_5 3 1 0 2 3 5 74 602 2
cert_coverFacet 4 330
cert_cover_2 4 2 0 5 7 74 330 3
cert_coverFacet 5 428
cert_cover_5 5 3 1 2 4 6 44 428 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_310

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/P0_311.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_311

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 397, 309, 677, 617, 297, 662, 458, 586, 626, 466, 564, 404, 376, 37, 133, 261, 41, 137, 265, 521, 289, 545, 641, 74, 138, 522, 82, 146, 530, 450, 578, 642, 52, 148, 276, 532, 548, 388, 644, 104, 296, 328, 584, 392, 112, 304, 560, 336, 400, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_397, vertices_309, vertices_677, vertices_617, vertices_297, vertices_662, vertices_458, vertices_586, vertices_626, vertices_466, vertices_564, vertices_404, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_41, vertices_137, vertices_265, vertices_521, vertices_289, vertices_545, vertices_641, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_450, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_532, vertices_548, vertices_388, vertices_644, vertices_104, vertices_296, vertices_328, vertices_584, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_400, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_397), (false, vertices_309), (false, vertices_677), (false, vertices_617), (false, vertices_297), (true, vertices_74), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_450), (true, vertices_578), (true, vertices_148), (true, vertices_532), (true, vertices_328), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_297) then 12 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_450) then 15 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 74 82 146 530 578 148 532 328 112 560 336 400 297 651 450 397 309 677 617
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
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 376
cert_cover_5 7 2 2 3 4 5 104 376 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_311

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2193 : Certifies 2193 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_278.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2194 : Certifies 2194 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_279.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2195 : Certifies 2195 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_280.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2196 : Certifies 2196 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_281.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2197 : Certifies 2197 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_282.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2198 : Certifies 2198 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_283.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2199 : Certifies 2199 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_284.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2200 : Certifies 2200 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_286.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2201 : Certifies 2201 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_287.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2202 : Certifies 2202 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_288.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2203 : Certifies 2203 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_289.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2204 : Certifies 2204 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_290.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2205 : Certifies 2205 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_291.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2206 : Certifies 2206 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_292.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2207 : Certifies 2207 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_293.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2208 : Certifies 2208 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_294.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2209 : Certifies 2209 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_295.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2210 : Certifies 2210 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_297.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2211 : Certifies 2211 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_298.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2212 : Certifies 2212 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_301.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2213 : Certifies 2213 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_302.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2214 : Certifies 2214 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_303.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2215 : Certifies 2215 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_304.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2216 : Certifies 2216 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_305.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2217 : Certifies 2217 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_306.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2218 : Certifies 2218 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_307.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2219 : Certifies 2219 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_308.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2220 : Certifies 2220 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_309.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2221 : Certifies 2221 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_310.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2222 : Certifies 2222 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_311.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B072 (j : Fin 30) :
    Certifies (2193 + j.val) := by
  fin_cases j
  · exact projection_2193
  · exact projection_2194
  · exact projection_2195
  · exact projection_2196
  · exact projection_2197
  · exact projection_2198
  · exact projection_2199
  · exact projection_2200
  · exact projection_2201
  · exact projection_2202
  · exact projection_2203
  · exact projection_2204
  · exact projection_2205
  · exact projection_2206
  · exact projection_2207
  · exact projection_2208
  · exact projection_2209
  · exact projection_2210
  · exact projection_2211
  · exact projection_2212
  · exact projection_2213
  · exact projection_2214
  · exact projection_2215
  · exact projection_2216
  · exact projection_2217
  · exact projection_2218
  · exact projection_2219
  · exact projection_2220
  · exact projection_2221
  · exact projection_2222

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
