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
/- Source: ProjectionCertificates/R_m16e10q1_0649.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0649

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 301, 405, 677, 281, 537, 721, 358, 218, 538, 298, 458, 626, 612, 964, 408, 37, 133, 261, 25, 41, 265, 521, 145, 273, 529, 545, 641, 26, 42, 202, 266, 522, 82, 530, 98, 290, 546, 322, 100, 292, 548, 324, 580, 388, 644, 152, 280, 536, 296, 392, 208, 592, 400, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_301, vertices_405, vertices_677, vertices_281, vertices_537, vertices_721, vertices_358, vertices_218, vertices_538, vertices_298, vertices_458, vertices_626, vertices_612, vertices_964, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_25, vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_545, vertices_641, vertices_26, vertices_42, vertices_202, vertices_266, vertices_522, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_152, vertices_280, vertices_536, vertices_296, vertices_392, vertices_208, vertices_592, vertices_400, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_301), (false, vertices_405), (false, vertices_677), (false, vertices_281), (false, vertices_537), (false, vertices_721), (true, vertices_26), (true, vertices_202), (true, vertices_266), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_100), (true, vertices_324), (true, vertices_580), (true, vertices_152), (true, vertices_392), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_448) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 281 1 537 26 266 82 530 98 290 322 100 324 580 152 392 608 448 555 202 301 405 677 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 0 1 4 5 7 358 98 1
cert_row_4 3 1 5 6 7 8 964 324 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 2 0 1 4 5 98 358 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 458
cert_cover_5 4 0 0 2 5 7 202 458 3
cert_coverFacet 5 626
cert_cover_5 5 1 0 3 4 5 82 626 2
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 964
cert_cover_5 7 3 1 5 6 7 324 964 2
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0649

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0650.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0650

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 333, 141, 709, 185, 281, 481, 782, 282, 538, 242, 722, 610, 802, 668, 868, 13, 69, 133, 25, 137, 265, 49, 273, 161, 289, 193, 321, 26, 266, 522, 50, 210, 274, 530, 98, 290, 546, 578, 770, 140, 268, 524, 324, 580, 644, 772, 152, 280, 536, 176, 656, 224, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_333, vertices_141, vertices_709, vertices_185, vertices_281, vertices_481, vertices_782, vertices_282, vertices_538, vertices_242, vertices_722, vertices_610, vertices_802, vertices_668, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_133, vertices_25, vertices_137, vertices_265, vertices_49, vertices_273, vertices_161, vertices_289, vertices_193, vertices_321, vertices_26, vertices_266, vertices_522, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_280, vertices_536, vertices_176, vertices_656, vertices_224, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_333), (false, vertices_141), (false, vertices_709), (false, vertices_185), (false, vertices_281), (false, vertices_481), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_210), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_524), (true, vertices_772), (true, vertices_536), (true, vertices_656), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_210) then 18 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_578) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_608) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 141 0 281 26 266 522 530 98 546 578 770 524 772 536 656 608 800 307 210 333 709 185 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 5 7 8 868 324 1
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 50 242 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 8 210 722 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 802
cert_cover_2 6 4 0 7 8 290 802 3
cert_coverFacet 7 668
cert_cover_5 7 3 1 2 3 6 140 668 2
cert_coverFacet 8 868
cert_cover_5 8 0 1 4 5 7 324 868 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0650

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0651.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0651

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 45, 333, 309, 617, 929, 454, 218, 602, 690, 898, 572, 156, 204, 404, 432, 13, 37, 261, 41, 73, 289, 545, 321, 577, 769, 90, 146, 530, 194, 322, 578, 386, 642, 770, 28, 44, 76, 140, 52, 148, 276, 196, 324, 388, 152, 536, 552, 200, 584, 176, 304, 560, 400, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_45, vertices_333, vertices_309, vertices_617, vertices_929, vertices_454, vertices_218, vertices_602, vertices_690, vertices_898, vertices_572, vertices_156, vertices_204, vertices_404, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_261, vertices_41, vertices_73, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_90, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_140, vertices_52, vertices_148, vertices_276, vertices_196, vertices_324, vertices_388, vertices_152, vertices_536, vertices_552, vertices_200, vertices_584, vertices_176, vertices_304, vertices_560, vertices_400, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_45), (false, vertices_333), (false, vertices_309), (false, vertices_617), (false, vertices_929), (true, vertices_90), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_28), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_176), (true, vertices_560), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_309) then 22 else
  if p.val = (false, vertices_617) then 24 else
  if p.val = (false, vertices_929) then 27 else
  if p.val = (true, vertices_90) then 19 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_560) then 15 else
  if p.val = (true, vertices_400) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_2 1 0 2 3 5 90
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 8 90 602 3
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 146 690 2
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 572
cert_cover_5 5 3 1 2 3 4 28 572 3
cert_coverFacet 6 156
cert_cover_2 6 2 1 3 6 28 156 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0651

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0652.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0652

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 613, 809, 113, 433, 721, 158, 302, 278, 714, 778, 402, 220, 556, 588, 372, 49, 81, 145, 97, 289, 545, 577, 385, 641, 769, 14, 22, 262, 138, 266, 522, 146, 274, 386, 642, 770, 156, 44, 76, 524, 84, 276, 100, 292, 548, 580, 296, 552, 200, 584, 776, 112, 304, 208, 400, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_613, vertices_809, vertices_113, vertices_433, vertices_721, vertices_158, vertices_302, vertices_278, vertices_714, vertices_778, vertices_402, vertices_220, vertices_556, vertices_588, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_145, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_156, vertices_44, vertices_76, vertices_524, vertices_84, vertices_276, vertices_100, vertices_292, vertices_548, vertices_580, vertices_296, vertices_552, vertices_200, vertices_584, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_613), (false, vertices_809), (false, vertices_113), (false, vertices_433), (false, vertices_721), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_200), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_274) then 8 else
  if p.val = (true, vertices_156) then 21 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_84) then 12 else
  if p.val = (true, vertices_276) then 13 else
  if p.val = (true, vertices_292) then 14 else
  if p.val = (true, vertices_200) then 15 else
  if p.val = (true, vertices_584) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 1 2 4 7 302 14 3
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 8 6 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 14 158 3
cert_coverFacet 1 302
cert_cover_5 1 2 0 1 2 4 14 302 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 714
cert_cover_5 3 0 0 2 5 6 138 714 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 5 156 220 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 588
cert_cover_2 8 2 1 5 8 76 588 3
cert_coverFacet 9 372
cert_cover_5 9 3 1 3 4 5 84 372 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0652

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0653.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0653

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 179, 291, 29, 589, 149, 313, 482, 898, 348, 628, 692, 968, 368, 736, 35, 131, 259, 515, 13, 21, 133, 517, 25, 265, 521, 49, 145, 289, 162, 290, 386, 642, 770, 28, 76, 564, 84, 148, 580, 644, 280, 328, 584, 776, 112, 176, 304, 336, 224, 352, 608, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_179, vertices_291, vertices_29, vertices_589, vertices_149, vertices_313, vertices_482, vertices_898, vertices_348, vertices_628, vertices_692, vertices_968, vertices_368, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_13, vertices_21, vertices_133, vertices_517, vertices_25, vertices_265, vertices_521, vertices_49, vertices_145, vertices_289, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_564, vertices_84, vertices_148, vertices_580, vertices_644, vertices_280, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_179), (false, vertices_291), (false, vertices_29), (false, vertices_589), (false, vertices_149), (false, vertices_313), (true, vertices_386), (true, vertices_564), (true, vertices_84), (true, vertices_328), (true, vertices_112), (true, vertices_336), (true, vertices_224), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_179) then 18 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_29) then 1 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_149) then 2 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_564) then 21 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_704) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_564), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 6 7 482 162 2
cert_row_2 1 1 3 4 8 564
cert_row_4 2 1 2 3 5 7 348 28 3
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 482
cert_cover_5 0 0 0 4 5 6 162 482 2
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 348
cert_cover_5 2 2 1 2 3 5 28 348 3
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 564 628 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 564 692 3
cert_coverFacet 5 968
cert_cover_5 5 3 2 5 6 7 328 968 2
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0653

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0654.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0654

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 789, 217, 281, 841, 737, 310, 534, 614, 410, 426, 674, 236, 300, 332, 836, 25, 73, 265, 145, 273, 529, 193, 577, 641, 769, 22, 38, 518, 394, 146, 274, 530, 162, 290, 546, 642, 44, 76, 268, 276, 532, 100, 292, 324, 580, 772, 152, 280, 168, 296, 200, 328, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_789, vertices_217, vertices_281, vertices_841, vertices_737, vertices_310, vertices_534, vertices_614, vertices_410, vertices_426, vertices_674, vertices_236, vertices_300, vertices_332, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_394, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_44, vertices_76, vertices_268, vertices_276, vertices_532, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_789), (false, vertices_217), (false, vertices_281), (false, vertices_841), (false, vertices_737), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_394), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_100), (true, vertices_292), (true, vertices_324), (true, vertices_580), (true, vertices_168), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 18 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_394) then 19 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_324) then 13 else
  if p.val = (true, vertices_580) then 14 else
  if p.val = (true, vertices_168) then 15 else
  if p.val = (true, vertices_296) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 5 38 614 3
cert_coverFacet 3 410
cert_cover_5 3 1 0 2 3 6 394 410 2
cert_coverFacet 4 426
cert_cover_5 4 1 0 2 4 6 394 426 2
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 44 236 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coverFacet 8 332
cert_cover_2 8 2 1 5 7 76 332 3
cert_coverFacet 9 836
cert_cover_2 9 5 1 7 8 324 836 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0654

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0655.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0655

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 675, 771, 613, 841, 481, 662, 602, 282, 778, 124, 412, 428, 596, 676, 360, 131, 259, 515, 97, 161, 545, 321, 577, 385, 769, 26, 266, 522, 146, 274, 530, 642, 770, 28, 44, 396, 84, 148, 532, 100, 164, 548, 580, 644, 88, 280, 104, 296, 328, 584, 776, 592, 400, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_675, vertices_771, vertices_613, vertices_841, vertices_481, vertices_662, vertices_602, vertices_282, vertices_778, vertices_124, vertices_412, vertices_428, vertices_596, vertices_676, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_28, vertices_44, vertices_396, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_88, vertices_280, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_592, vertices_400, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_675), (false, vertices_771), (false, vertices_613), (false, vertices_841), (false, vertices_481), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_396), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_675) then 19 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_396) then 22 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_104) then 14 else
  if p.val = (true, vertices_296) then 15 else
  if p.val = (true, vertices_592) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 1 2 3 4 5 124 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 124
cert_cover_5 4 3 1 2 3 4 28 124 3
cert_coverFacet 5 412
cert_cover_5 5 0 1 2 3 6 28 412 3
cert_coverFacet 6 428
cert_cover_5 6 0 1 2 4 6 44 428 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coverFacet 9 360
cert_cover_2 9 4 2 5 7 104 360 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0655

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0656.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0656

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 661, 681, 241, 337, 865, 206, 270, 214, 534, 806, 346, 300, 556, 652, 488, 81, 145, 273, 529, 97, 161, 545, 321, 641, 769, 14, 22, 198, 262, 518, 74, 266, 82, 274, 530, 770, 44, 140, 268, 524, 148, 532, 292, 548, 644, 168, 296, 552, 200, 328, 648, 208, 336, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_661, vertices_681, vertices_241, vertices_337, vertices_865, vertices_206, vertices_270, vertices_214, vertices_534, vertices_806, vertices_346, vertices_300, vertices_556, vertices_652, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_198, vertices_262, vertices_518, vertices_74, vertices_266, vertices_82, vertices_274, vertices_530, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_292, vertices_548, vertices_644, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_648, vertices_208, vertices_336, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_661), (false, vertices_681), (false, vertices_241), (false, vertices_337), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_266), (true, vertices_82), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_296), (true, vertices_200), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 19 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_82) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_548) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_200) then 15 else
  if p.val = (true, vertices_328) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 337 14 22 262 518 74 266 82 44 140 268 524 292 548 296 200 328 787 198 661 681 241 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_2 1 0 1 5 6 198
cert_row_4 2 0 2 3 5 7 346 74 2
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 214
cert_cover_5 2 1 0 1 3 5 22 214 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 806
cert_cover_5 4 0 0 1 4 7 262 806 2
cert_coverFacet 5 346
cert_cover_5 5 2 0 2 3 5 74 346 2
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 652
cert_cover_2 8 2 1 6 8 140 652 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 168 488 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0656

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0657.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0657

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 285, 149, 901, 185, 777, 737, 342, 218, 282, 234, 778, 354, 802, 724, 868, 21, 133, 261, 25, 41, 265, 521, 145, 161, 545, 641, 769, 26, 42, 202, 266, 522, 82, 274, 98, 290, 546, 322, 770, 84, 148, 276, 324, 580, 644, 772, 152, 280, 168, 776, 208, 224, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_285, vertices_149, vertices_901, vertices_185, vertices_777, vertices_737, vertices_342, vertices_218, vertices_282, vertices_234, vertices_778, vertices_354, vertices_802, vertices_724, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_25, vertices_41, vertices_265, vertices_521, vertices_145, vertices_161, vertices_545, vertices_641, vertices_769, vertices_26, vertices_42, vertices_202, vertices_266, vertices_522, vertices_82, vertices_274, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_84, vertices_148, vertices_276, vertices_324, vertices_580, vertices_644, vertices_772, vertices_152, vertices_280, vertices_168, vertices_776, vertices_208, vertices_224, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_285), (false, vertices_149), (false, vertices_901), (false, vertices_185), (false, vertices_777), (false, vertices_737), (true, vertices_26), (true, vertices_202), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_770), (true, vertices_84), (true, vertices_324), (true, vertices_580), (true, vertices_208), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_285) then 20 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_800) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 149 0 777 26 266 82 274 98 290 322 770 84 324 580 208 352 800 555 202 285 901 185 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 3 5 7 342 82 1
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 1 4 5 7 8 868 324 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 82 342 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 234
cert_cover_5 3 0 0 2 4 5 42 234 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 802
cert_cover_2 6 4 0 7 8 290 802 3
cert_coverFacet 7 724
cert_cover_5 7 2 1 3 5 6 84 724 3
cert_coverFacet 8 868
cert_cover_5 8 3 1 4 5 7 324 868 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0657

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0659.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0659

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 395, 643, 357, 709, 217, 361, 434, 722, 786, 620, 820, 184, 568, 600, 424, 131, 259, 515, 69, 261, 517, 73, 137, 265, 353, 193, 641, 146, 274, 530, 386, 642, 770, 100, 292, 548, 580, 772, 56, 88, 152, 536, 104, 168, 296, 552, 584, 392, 176, 304, 560, 208, 592, 784, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_395, vertices_643, vertices_357, vertices_709, vertices_217, vertices_361, vertices_434, vertices_722, vertices_786, vertices_620, vertices_820, vertices_184, vertices_568, vertices_600, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_353, vertices_193, vertices_641, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_552, vertices_584, vertices_392, vertices_176, vertices_304, vertices_560, vertices_208, vertices_592, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_395), (false, vertices_643), (false, vertices_357), (false, vertices_709), (false, vertices_217), (false, vertices_361), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_548), (true, vertices_56), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_584), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 24 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_357) then 25 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_361) then 26 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_784) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 8 620 100 1
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 1 3 4 7 8 820 292 1
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 434
cert_cover_5 0 2 0 3 4 6 146 434 2
cert_coverFacet 1 722
cert_cover_5 1 1 0 3 5 6 146 722 2
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 620
cert_cover_5 3 0 1 2 4 5 100 620 1
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 292 820 1
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0659

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0660.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0660

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 301, 169, 713, 689, 865, 206, 270, 566, 214, 774, 338, 786, 188, 804, 976, 41, 73, 137, 265, 161, 289, 545, 321, 577, 641, 14, 22, 198, 262, 518, 74, 266, 82, 274, 530, 322, 770, 44, 140, 268, 52, 148, 292, 548, 772, 168, 200, 176, 560, 208, 336, 656, 784, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_301, vertices_169, vertices_713, vertices_689, vertices_865, vertices_206, vertices_270, vertices_566, vertices_214, vertices_774, vertices_338, vertices_786, vertices_188, vertices_804, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_265, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_14, vertices_22, vertices_198, vertices_262, vertices_518, vertices_74, vertices_266, vertices_82, vertices_274, vertices_530, vertices_322, vertices_770, vertices_44, vertices_140, vertices_268, vertices_52, vertices_148, vertices_292, vertices_548, vertices_772, vertices_168, vertices_200, vertices_176, vertices_560, vertices_208, vertices_336, vertices_656, vertices_784, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_301), (false, vertices_169), (false, vertices_713), (false, vertices_689), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_140), (true, vertices_52), (true, vertices_148), (true, vertices_548), (true, vertices_772), (true, vertices_208), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_301) then 21 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (false, vertices_865) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 19 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 169 14 22 262 518 82 274 530 770 140 52 148 548 772 208 336 784 331 198 301 713 689 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 6 188 44 2
cert_row_4 1 0 1 3 4 8 566 22 3
cert_row_2 2 0 1 5 6 198
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 2 4 0 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 566
cert_cover_5 2 1 0 1 3 4 22 566 3
cert_coverFacet 3 214
cert_cover_5 3 2 0 1 3 5 22 214 3
cert_coverFacet 4 774
cert_cover_2 4 1 0 7 8 262 774 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 786
cert_cover_2 6 3 0 7 8 274 786 3
cert_coverFacet 7 188
cert_cover_5 7 0 1 2 3 4 44 188 2
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coverFacet 9 976
cert_cover_5 9 3 3 5 6 7 208 976 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0660

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0661.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0661

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 661, 361, 241, 337, 929, 206, 270, 214, 534, 806, 346, 300, 556, 652, 744, 81, 145, 273, 529, 97, 161, 289, 321, 641, 769, 14, 22, 198, 262, 518, 74, 266, 82, 274, 530, 770, 44, 140, 268, 524, 148, 532, 292, 548, 644, 104, 296, 552, 200, 328, 648, 208, 336, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_661, vertices_361, vertices_241, vertices_337, vertices_929, vertices_206, vertices_270, vertices_214, vertices_534, vertices_806, vertices_346, vertices_300, vertices_556, vertices_652, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_198, vertices_262, vertices_518, vertices_74, vertices_266, vertices_82, vertices_274, vertices_530, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_292, vertices_548, vertices_644, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_648, vertices_208, vertices_336, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_661), (false, vertices_361), (false, vertices_241), (false, vertices_337), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_266), (true, vertices_82), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_552), (true, vertices_200), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_929) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 19 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_82) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_548) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_200) then 15 else
  if p.val = (true, vertices_648) then 16 else
  0
cert_priority
cert_nodeAtPriority_66 337 14 22 262 518 74 266 82 44 140 268 524 292 548 552 200 648 787 198 661 361 241 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 74 2
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_2 2 0 1 5 6 198
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 7 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 214
cert_cover_5 2 2 0 1 3 5 22 214 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 806
cert_cover_5 4 1 0 1 4 7 262 806 2
cert_coverFacet 5 346
cert_cover_5 5 0 0 2 3 5 74 346 2
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 652
cert_cover_2 8 2 1 6 8 140 652 3
cert_coverFacet 9 744
cert_cover_5 9 3 2 4 5 6 104 744 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0661

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0662.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0662

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [43, 395, 611, 771, 453, 233, 849, 286, 58, 818, 668, 396, 340, 596, 740, 696, 11, 35, 259, 515, 41, 137, 97, 193, 321, 577, 385, 769, 26, 42, 266, 50, 274, 546, 770, 28, 140, 268, 84, 276, 532, 196, 324, 580, 388, 644, 56, 664, 168, 392, 560, 336, 592, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_43, vertices_395, vertices_611, vertices_771, vertices_453, vertices_233, vertices_849, vertices_286, vertices_58, vertices_818, vertices_668, vertices_396, vertices_340, vertices_596, vertices_740, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_41, vertices_137, vertices_97, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_26, vertices_42, vertices_266, vertices_50, vertices_274, vertices_546, vertices_770, vertices_28, vertices_140, vertices_268, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_56, vertices_664, vertices_168, vertices_392, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_43), (false, vertices_395), (false, vertices_611), (false, vertices_771), (false, vertices_453), (false, vertices_233), (false, vertices_849), (true, vertices_26), (true, vertices_50), (true, vertices_274), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_580), (true, vertices_644), (true, vertices_56), (true, vertices_664), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_611) then 18 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_664) then 23 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 5 6 8 740 196 1
cert_row_2 1 2 3 6 8 664
cert_row_4 2 0 1 2 3 7 286 26 1
cert_row_4 3 0 3 4 7 8 818 50 3
cert_rows
cert_pivot_2 5 6 1 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 26 286 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 818
cert_cover_5 2 3 0 3 4 7 50 818 3
cert_coverFacet 3 668
cert_cover_5 3 1 1 2 3 6 28 668 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 740
cert_cover_5 7 0 1 4 5 6 196 740 1
cert_coverFacet 8 696
cert_cover_5 8 1 2 3 4 6 56 696 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0662

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0663.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0663

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 789, 677, 453, 425, 777, 710, 122, 586, 434, 466, 674, 604, 340, 312, 792, 133, 261, 517, 41, 265, 521, 161, 545, 385, 769, 42, 74, 522, 50, 82, 402, 162, 546, 194, 578, 642, 84, 276, 532, 196, 324, 580, 644, 56, 88, 280, 536, 296, 584, 776, 304, 336, 784, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_789, vertices_677, vertices_453, vertices_425, vertices_777, vertices_710, vertices_122, vertices_586, vertices_434, vertices_466, vertices_674, vertices_604, vertices_340, vertices_312, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_161, vertices_545, vertices_385, vertices_769, vertices_42, vertices_74, vertices_522, vertices_50, vertices_82, vertices_402, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_584, vertices_776, vertices_304, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_789), (false, vertices_677), (false, vertices_453), (false, vertices_425), (false, vertices_777), (true, vertices_74), (true, vertices_50), (true, vertices_82), (true, vertices_402), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_84), (true, vertices_580), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_584), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 24 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_453) then 23 else
  if p.val = (false, vertices_425) then 25 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_402) then 19 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_584) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
cert_nodeAtPriority_63 777 74 50 82 162 194 578 642 84 580 56 88 280 536 584 304 336 555 402 789 677 453 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 6 7 402
cert_row_4 1 0 1 5 6 8 710 194 1
cert_row_4 2 0 2 3 4 5 122 42 2
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 1 0 1 5 6 194 710 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 42 122 2
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 6 50 434 3
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 6 82 466 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 84 604 1
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0663

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0664.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0664

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 613, 421, 197, 313, 553, 905, 214, 842, 434, 338, 898, 572, 604, 180, 344, 37, 69, 133, 41, 265, 521, 289, 545, 193, 577, 385, 641, 82, 146, 274, 194, 322, 578, 386, 642, 770, 540, 52, 84, 148, 164, 548, 196, 580, 56, 88, 280, 552, 328, 584, 776, 176, 304, 336, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_613, vertices_421, vertices_197, vertices_313, vertices_553, vertices_905, vertices_214, vertices_842, vertices_434, vertices_338, vertices_898, vertices_572, vertices_604, vertices_180, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_41, vertices_265, vertices_521, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_540, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_56, vertices_88, vertices_280, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_336, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_613), (false, vertices_421), (false, vertices_197), (false, vertices_313), (false, vertices_553), (false, vertices_905), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_540), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_88), (true, vertices_328), (true, vertices_584), (true, vertices_176), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_540) then 21 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_176) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_4 1 0 1 3 5 6 214 82 1
cert_row_2 2 1 2 3 8 540
cert_row_4 3 0 2 5 7 8 842 322 1
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 82 214 1
cert_coverFacet 1 842
cert_cover_5 1 3 0 2 5 7 322 842 1
cert_coverFacet 2 434
cert_cover_5 2 0 0 3 4 6 146 434 2
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 572
cert_cover_5 5 2 1 2 3 4 540 572 3
cert_coverFacet 6 604
cert_cover_5 6 2 1 2 3 5 540 604 3
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0664

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0665.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0665

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 267, 675, 771, 613, 233, 841, 662, 282, 850, 412, 428, 372, 596, 676, 360, 11, 131, 259, 515, 73, 137, 265, 97, 161, 545, 577, 769, 26, 266, 146, 274, 530, 642, 770, 396, 84, 148, 276, 532, 100, 164, 292, 548, 580, 644, 152, 280, 104, 168, 296, 328, 336, 592, 352, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_267, vertices_675, vertices_771, vertices_613, vertices_233, vertices_841, vertices_662, vertices_282, vertices_850, vertices_412, vertices_428, vertices_372, vertices_596, vertices_676, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_545, vertices_577, vertices_769, vertices_26, vertices_266, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_396, vertices_84, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_292, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_328, vertices_336, vertices_592, vertices_352, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_267), (false, vertices_675), (false, vertices_771), (false, vertices_613), (false, vertices_233), (false, vertices_841), (true, vertices_274), (true, vertices_530), (true, vertices_396), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_644), (true, vertices_280), (true, vertices_296), (true, vertices_336), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 17 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_841) then 24 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_396) then 21 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 1 3 6 8 662 146 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 1 3 4 5 7 372 84 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 146 662 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 274 850 2
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 396 412 2
cert_coverFacet 4 428
cert_cover_5 4 0 1 2 4 6 396 428 2
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 84 372 2
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0665

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0666.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0666

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 589, 569, 89, 177, 465, 865, 654, 358, 614, 390, 690, 348, 396, 408, 664, 25, 73, 521, 49, 81, 145, 161, 289, 545, 321, 577, 385, 102, 134, 262, 518, 162, 290, 546, 386, 642, 76, 140, 268, 524, 324, 580, 388, 88, 152, 280, 536, 392, 648, 176, 560, 336, 400, 656, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_589, vertices_569, vertices_89, vertices_177, vertices_465, vertices_865, vertices_654, vertices_358, vertices_614, vertices_390, vertices_690, vertices_348, vertices_396, vertices_408, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_521, vertices_49, vertices_81, vertices_145, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_102, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_388, vertices_88, vertices_152, vertices_280, vertices_536, vertices_392, vertices_648, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_589), (false, vertices_569), (false, vertices_89), (false, vertices_177), (false, vertices_465), (false, vertices_865), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_546), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_648), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_102) then 18 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_89), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 7 348 76 2
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 1 2 6 8 654 134 2
cert_row_4 3 0 3 4 6 8 690 162 1
cert_rows
cert_pivot_2 7 5 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 134 654 2
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 7 102 358 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 8 102 614 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 162 690 1
cert_coverFacet 5 348
cert_cover_5 5 0 1 2 3 5 76 348 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 664
cert_cover_2 8 3 2 6 8 152 664 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0666

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0667.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0667

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 541, 149, 709, 625, 433, 449, 782, 122, 602, 298, 962, 156, 428, 900, 184, 21, 133, 517, 49, 145, 529, 97, 289, 193, 321, 577, 385, 90, 42, 266, 522, 98, 290, 322, 578, 770, 28, 140, 268, 524, 148, 388, 644, 772, 56, 152, 536, 168, 296, 112, 176, 592, 416, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_541, vertices_149, vertices_709, vertices_625, vertices_433, vertices_449, vertices_782, vertices_122, vertices_602, vertices_298, vertices_962, vertices_156, vertices_428, vertices_900, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_49, vertices_145, vertices_529, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_90, vertices_42, vertices_266, vertices_522, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_112, vertices_176, vertices_592, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_541), (false, vertices_149), (false, vertices_709), (false, vertices_625), (false, vertices_433), (false, vertices_449), (true, vertices_90), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_388), (true, vertices_772), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 90 122 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 322 962 2
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 140 428 2
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0667

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0668.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0668

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 339, 387, 565, 85, 421, 793, 801, 842, 930, 706, 124, 236, 696, 344, 712, 67, 131, 259, 21, 37, 69, 133, 81, 273, 529, 289, 545, 385, 769, 194, 322, 578, 386, 642, 770, 108, 52, 84, 164, 196, 56, 88, 280, 536, 168, 200, 328, 584, 648, 776, 560, 336, 416, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_339, vertices_387, vertices_565, vertices_85, vertices_421, vertices_793, vertices_801, vertices_842, vertices_930, vertices_706, vertices_124, vertices_236, vertices_696, vertices_344, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_21, vertices_37, vertices_69, vertices_133, vertices_81, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_769, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_108, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_280, vertices_536, vertices_168, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_560, vertices_336, vertices_416, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_339), (false, vertices_387), (false, vertices_565), (false, vertices_85), (false, vertices_421), (false, vertices_793), (false, vertices_801), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_108), (true, vertices_56), (true, vertices_88), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 18 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_565) then 22 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_801) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_108) then 20 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 4 6 7 8 930 386 1
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 1 0 2 5 7 322 842 1
cert_coverFacet 1 930
cert_cover_5 1 2 0 4 6 7 386 930 1
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 4 108 124 2
cert_coverFacet 4 236
cert_cover_5 4 0 1 2 4 6 108 236 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0668

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0669.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0669

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 331, 227, 771, 121, 297, 929, 214, 342, 774, 668, 284, 812, 568, 344, 752, 67, 131, 259, 515, 41, 73, 265, 97, 161, 289, 641, 769, 86, 134, 262, 518, 194, 322, 770, 28, 268, 524, 148, 276, 644, 772, 56, 88, 280, 536, 296, 552, 328, 112, 560, 208, 336, 656, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_331, vertices_227, vertices_771, vertices_121, vertices_297, vertices_929, vertices_214, vertices_342, vertices_774, vertices_668, vertices_284, vertices_812, vertices_568, vertices_344, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_41, vertices_73, vertices_265, vertices_97, vertices_161, vertices_289, vertices_641, vertices_769, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_770, vertices_28, vertices_268, vertices_524, vertices_148, vertices_276, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_112, vertices_560, vertices_208, vertices_336, vertices_656, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_331), (false, vertices_227), (false, vertices_771), (false, vertices_121), (false, vertices_297), (false, vertices_929), (true, vertices_86), (true, vertices_262), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_331) then 20 else
  if p.val = (false, vertices_227) then 21 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_121) then 23 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_929) then 26 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_656) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 0 771 1 297 262 28 268 524 148 276 772 280 536 552 560 208 336 656 647 86 331 227 121 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 1 2 4 7 8 812 268 2
cert_row_4 2 1 2 3 6 8 668 28 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 668
cert_cover_5 3 2 1 2 3 6 28 668 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 812
cert_cover_5 5 1 1 2 4 7 268 812 2
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0669

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0670.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0670

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 61, 77, 341, 233, 561, 865, 902, 186, 410, 562, 738, 284, 716, 396, 836, 13, 21, 69, 41, 73, 49, 273, 529, 97, 545, 321, 769, 154, 50, 274, 530, 162, 546, 386, 642, 770, 28, 76, 140, 268, 276, 324, 580, 388, 644, 772, 56, 280, 168, 200, 392, 560, 224, 608, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_61, vertices_77, vertices_341, vertices_233, vertices_561, vertices_865, vertices_902, vertices_186, vertices_410, vertices_562, vertices_738, vertices_284, vertices_716, vertices_396, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_41, vertices_73, vertices_49, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_769, vertices_154, vertices_50, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_140, vertices_268, vertices_276, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_168, vertices_200, vertices_392, vertices_560, vertices_224, vertices_608, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_61), (false, vertices_77), (false, vertices_341), (false, vertices_233), (false, vertices_561), (false, vertices_865), (true, vertices_154), (true, vertices_50), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_280), (true, vertices_392), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_61) then 20 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_341) then 21 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_704) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 1 77 0 561 50 162 546 386 642 140 268 580 388 644 772 280 392 704 787 154 61 341 233 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 154 186 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 76 716 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 836
cert_cover_2 8 5 1 7 8 324 836 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0670

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0671.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0671

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 397, 213, 613, 773, 233, 297, 286, 666, 682, 298, 850, 156, 340, 836, 752, 69, 133, 261, 517, 41, 137, 265, 97, 289, 545, 193, 769, 26, 42, 650, 266, 274, 530, 290, 546, 770, 28, 140, 268, 84, 148, 276, 324, 580, 772, 152, 168, 296, 208, 336, 592, 656, 224, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_397, vertices_213, vertices_613, vertices_773, vertices_233, vertices_297, vertices_286, vertices_666, vertices_682, vertices_298, vertices_850, vertices_156, vertices_340, vertices_836, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_265, vertices_97, vertices_289, vertices_545, vertices_193, vertices_769, vertices_26, vertices_42, vertices_650, vertices_266, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_324, vertices_580, vertices_772, vertices_152, vertices_168, vertices_296, vertices_208, vertices_336, vertices_592, vertices_656, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_397), (false, vertices_213), (false, vertices_613), (false, vertices_773), (false, vertices_233), (false, vertices_297), (true, vertices_26), (true, vertices_42), (true, vertices_650), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_276), (true, vertices_324), (true, vertices_152), (true, vertices_336), (true, vertices_592), (true, vertices_656), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_650) then 18 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_672) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 773 1 297 26 42 266 274 530 28 276 324 152 336 592 656 672 832 803 650 397 213 613 233
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_2 1 0 2 6 8 650
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 3 4 5 6 8 752 208 1
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 26 666 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 42 682 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 274 850 2
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 208 752 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0671

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0672.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0672

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 789, 421, 709, 57, 281, 689, 590, 454, 774, 122, 778, 482, 728, 792, 240, 133, 261, 517, 25, 41, 265, 49, 273, 529, 161, 289, 641, 70, 262, 518, 42, 74, 266, 522, 98, 290, 450, 770, 196, 580, 388, 772, 56, 88, 280, 536, 584, 776, 112, 176, 208, 656, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_789, vertices_421, vertices_709, vertices_57, vertices_281, vertices_689, vertices_590, vertices_454, vertices_774, vertices_122, vertices_778, vertices_482, vertices_728, vertices_792, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_41, vertices_265, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_70, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_290, vertices_450, vertices_770, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_789), (false, vertices_421), (false, vertices_709), (false, vertices_57), (false, vertices_281), (false, vertices_689), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_450), (true, vertices_770), (true, vertices_88), (true, vertices_536), (true, vertices_584), (true, vertices_776), (true, vertices_112), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_450) then 18 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_21 0 57 1 281 70 262 518 74 522 98 770 88 536 584 776 112 208 224 299 450 789 421 709 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 7 450
cert_row_4 1 0 1 2 5 8 590 70 2
cert_row_4 2 0 2 3 4 5 122 42 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 42 122 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 482
cert_cover_5 5 0 0 4 5 6 98 482 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0672

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0673.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0673

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 555, 707, 565, 597, 57, 465, 902, 394, 778, 812, 116, 484, 708, 376, 408, 11, 131, 515, 533, 25, 41, 49, 81, 145, 545, 193, 577, 138, 266, 522, 386, 642, 770, 52, 84, 100, 292, 548, 196, 580, 388, 644, 772, 56, 152, 280, 296, 552, 392, 776, 112, 336, 400, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_555, vertices_707, vertices_565, vertices_597, vertices_57, vertices_465, vertices_902, vertices_394, vertices_778, vertices_812, vertices_116, vertices_484, vertices_708, vertices_376, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_515, vertices_533, vertices_25, vertices_41, vertices_49, vertices_81, vertices_145, vertices_545, vertices_193, vertices_577, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_776, vertices_112, vertices_336, vertices_400, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_555), (false, vertices_707), (false, vertices_565), (false, vertices_597), (false, vertices_57), (false, vertices_465), (true, vertices_266), (true, vertices_386), (true, vertices_770), (true, vertices_100), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 17 else
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_597) then 22 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_465) then 25 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 1 2 4 7 8 812 292 1
cert_row_4 2 1 4 5 6 7 484 100 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 292 812 1
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 484
cert_cover_5 5 2 1 4 5 6 100 484 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 56 376 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0673

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0674.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0674

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 339, 147, 617, 329, 721, 310, 150, 774, 812, 180, 740, 440, 472, 232, 19, 131, 259, 515, 73, 265, 521, 81, 145, 321, 577, 641, 22, 134, 262, 518, 146, 274, 770, 52, 148, 164, 292, 548, 644, 772, 408, 104, 168, 296, 552, 200, 328, 776, 176, 304, 208, 336, 224, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_339, vertices_147, vertices_617, vertices_329, vertices_721, vertices_310, vertices_150, vertices_774, vertices_812, vertices_180, vertices_740, vertices_440, vertices_472, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_321, vertices_577, vertices_641, vertices_22, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_770, vertices_52, vertices_148, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_408, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_339), (false, vertices_147), (false, vertices_617), (false, vertices_329), (false, vertices_721), (true, vertices_22), (true, vertices_262), (true, vertices_52), (true, vertices_148), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_408), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_176), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 21 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_339) then 19 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
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
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_2 1 2 3 6 7 408
cert_row_4 2 1 2 4 7 8 812 292 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 292 812 1
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 740
cert_cover_5 5 3 1 4 5 6 164 740 2
cert_coverFacet 6 440
cert_cover_5 6 1 2 3 4 6 408 440 2
cert_coverFacet 7 472
cert_cover_5 7 1 2 3 5 6 408 472 2
cert_coverFacet 8 232
cert_cover_2 8 4 2 5 6 104 232 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0674

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0675.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0675

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 117, 277, 805, 601, 105, 681, 406, 714, 210, 594, 930, 364, 460, 212, 424, 21, 37, 261, 41, 73, 521, 81, 273, 529, 97, 545, 769, 82, 146, 274, 530, 194, 578, 386, 642, 770, 332, 84, 148, 276, 100, 292, 196, 388, 104, 168, 296, 200, 584, 392, 648, 208, 592, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_117, vertices_277, vertices_805, vertices_601, vertices_105, vertices_681, vertices_406, vertices_714, vertices_210, vertices_594, vertices_930, vertices_364, vertices_460, vertices_212, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_41, vertices_73, vertices_521, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_332, vertices_84, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_388, vertices_104, vertices_168, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_208, vertices_592, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_117), (false, vertices_277), (false, vertices_805), (false, vertices_601), (false, vertices_105), (false, vertices_681), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_332), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_332) then 21 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_2 1 1 2 5 7 332
cert_row_4 2 0 2 5 6 8 714 194 1
cert_row_4 3 0 4 6 7 8 930 386 1
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 714
cert_cover_5 1 2 0 2 5 6 194 714 1
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 930
cert_cover_5 4 3 0 4 6 7 386 930 1
cert_coverFacet 5 364
cert_cover_5 5 1 1 2 4 5 332 364 2
cert_coverFacet 6 460
cert_cover_5 6 1 1 2 5 6 332 460 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0675

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0676.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0676

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 523, 595, 397, 793, 241, 401, 654, 678, 226, 866, 812, 372, 180, 404, 848, 11, 67, 515, 137, 265, 521, 81, 145, 273, 529, 193, 385, 646, 138, 522, 98, 162, 546, 194, 578, 140, 268, 524, 52, 148, 276, 164, 292, 548, 388, 776, 112, 176, 336, 592, 400, 784, 224, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_523, vertices_595, vertices_397, vertices_793, vertices_241, vertices_401, vertices_654, vertices_678, vertices_226, vertices_866, vertices_812, vertices_372, vertices_180, vertices_404, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_515, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_385, vertices_646, vertices_138, vertices_522, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_388, vertices_776, vertices_112, vertices_176, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_523), (false, vertices_595), (false, vertices_397), (false, vertices_793), (false, vertices_241), (false, vertices_401), (true, vertices_646), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_524), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_336), (true, vertices_352), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_595) then 18 else
  if p.val = (false, vertices_397) then 21 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_646) then 19 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_800) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_646), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 646 654 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 646 678 2
cert_coverFacet 2 226
cert_cover_2 2 4 0 5 6 98 226 3
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 98 866 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 268 812 2
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 52 372 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0676

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0677.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0677

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 77, 613, 901, 457, 241, 673, 542, 774, 282, 626, 306, 930, 604, 440, 216, 13, 69, 261, 517, 73, 265, 97, 161, 545, 193, 385, 641, 14, 262, 518, 26, 266, 50, 274, 530, 290, 546, 770, 540, 76, 580, 772, 88, 152, 280, 200, 392, 112, 176, 304, 208, 592, 608, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_77, vertices_613, vertices_901, vertices_457, vertices_241, vertices_673, vertices_542, vertices_774, vertices_282, vertices_626, vertices_306, vertices_930, vertices_604, vertices_440, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_73, vertices_265, vertices_97, vertices_161, vertices_545, vertices_193, vertices_385, vertices_641, vertices_14, vertices_262, vertices_518, vertices_26, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_540, vertices_76, vertices_580, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_392, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_608, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_77), (false, vertices_613), (false, vertices_901), (false, vertices_457), (false, vertices_241), (false, vertices_673), (true, vertices_518), (true, vertices_26), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_540), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_304), (true, vertices_592), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 21 18 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 17 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_901) then 23 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_241) then 25 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_540) then 20 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_592) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 8 540
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 0 4 6 7 8 930 290 2
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 626
cert_cover_5 3 1 0 3 4 5 50 626 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 930
cert_cover_5 5 2 0 4 6 7 290 930 2
cert_coverFacet 6 604
cert_cover_5 6 0 1 2 3 5 540 604 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 152 440 2
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0677

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0678.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0678

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 589, 405, 677, 793, 417, 710, 842, 242, 354, 674, 212, 120, 440, 360, 77, 21, 133, 517, 25, 521, 273, 161, 289, 545, 385, 769, 98, 162, 290, 546, 194, 322, 578, 642, 770, 84, 148, 196, 580, 644, 56, 88, 280, 104, 296, 328, 584, 776, 112, 176, 208, 400, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_589, vertices_405, vertices_677, vertices_793, vertices_417, vertices_710, vertices_842, vertices_242, vertices_354, vertices_674, vertices_212, vertices_120, vertices_440, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_21, vertices_133, vertices_517, vertices_25, vertices_521, vertices_273, vertices_161, vertices_289, vertices_545, vertices_385, vertices_769, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_84, vertices_148, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_589), (false, vertices_405), (false, vertices_677), (false, vertices_793), (false, vertices_417), (true, vertices_98), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_196), (true, vertices_56), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 22 18 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_405) then 23 else
  if p.val = (false, vertices_677) then 24 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 3 4 5 6 242 98 1
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 242
cert_cover_5 2 2 0 3 4 5 98 242 1
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 56 440 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0678

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0679.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0679

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 541, 149, 709, 241, 817, 833, 398, 122, 218, 298, 962, 156, 812, 900, 568, 21, 133, 517, 49, 145, 529, 97, 289, 193, 321, 577, 769, 90, 42, 138, 266, 98, 290, 194, 322, 386, 28, 140, 268, 524, 148, 388, 644, 772, 56, 152, 536, 296, 552, 112, 560, 208, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_541, vertices_149, vertices_709, vertices_241, vertices_817, vertices_833, vertices_398, vertices_122, vertices_218, vertices_298, vertices_962, vertices_156, vertices_812, vertices_900, vertices_568] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_49, vertices_145, vertices_529, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_769, vertices_90, vertices_42, vertices_138, vertices_266, vertices_98, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_296, vertices_552, vertices_112, vertices_560, vertices_208, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_541), (false, vertices_149), (false, vertices_709), (false, vertices_241), (false, vertices_817), (false, vertices_833), (true, vertices_90), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_268), (true, vertices_388), (true, vertices_772), (true, vertices_56), (true, vertices_152), (true, vertices_296), (true, vertices_552), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 17 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_817) then 25 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_90) then 18 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 2 6 7 398 138 1
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 138 398 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 90 122 3
cert_coverFacet 2 218
cert_cover_5 2 0 0 2 3 6 90 218 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 194 962 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 812
cert_cover_5 6 3 1 2 4 7 268 812 2
cert_coverFacet 7 900
cert_cover_2 7 6 1 7 8 388 900 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0679

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4533 : Certifies 4533 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0649.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4534 : Certifies 4534 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0650.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4535 : Certifies 4535 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0651.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4536 : Certifies 4536 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0652.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4537 : Certifies 4537 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0653.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4538 : Certifies 4538 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0654.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4539 : Certifies 4539 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0655.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4540 : Certifies 4540 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0656.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4541 : Certifies 4541 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0657.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4542 : Certifies 4542 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0659.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4543 : Certifies 4543 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0660.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4544 : Certifies 4544 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0661.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4545 : Certifies 4545 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0662.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4546 : Certifies 4546 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0663.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4547 : Certifies 4547 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0664.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4548 : Certifies 4548 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0665.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4549 : Certifies 4549 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0666.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4550 : Certifies 4550 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0667.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4551 : Certifies 4551 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0668.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4552 : Certifies 4552 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0669.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4553 : Certifies 4553 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0670.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4554 : Certifies 4554 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0671.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4555 : Certifies 4555 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0672.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4556 : Certifies 4556 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0673.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4557 : Certifies 4557 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0674.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4558 : Certifies 4558 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0675.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4559 : Certifies 4559 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0676.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4560 : Certifies 4560 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0677.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4561 : Certifies 4561 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0678.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4562 : Certifies 4562 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0679.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B150 (j : Fin 30) :
    Certifies (4533 + j.val) := by
  fin_cases j
  · exact projection_4533
  · exact projection_4534
  · exact projection_4535
  · exact projection_4536
  · exact projection_4537
  · exact projection_4538
  · exact projection_4539
  · exact projection_4540
  · exact projection_4541
  · exact projection_4542
  · exact projection_4543
  · exact projection_4544
  · exact projection_4545
  · exact projection_4546
  · exact projection_4547
  · exact projection_4548
  · exact projection_4549
  · exact projection_4550
  · exact projection_4551
  · exact projection_4552
  · exact projection_4553
  · exact projection_4554
  · exact projection_4555
  · exact projection_4556
  · exact projection_4557
  · exact projection_4558
  · exact projection_4559
  · exact projection_4560
  · exact projection_4561
  · exact projection_4562

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
