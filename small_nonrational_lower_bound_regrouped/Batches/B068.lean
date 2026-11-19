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
/- Source: ProjectionCertificates/P0_103.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_103

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 551, 789, 409, 689, 481, 590, 326, 738, 354, 284, 540, 460, 728, 39, 261, 517, 145, 273, 529, 161, 289, 545, 385, 70, 262, 518, 98, 290, 546, 322, 578, 28, 76, 268, 524, 276, 532, 324, 152, 280, 536, 200, 584, 392, 656, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_551, vertices_789, vertices_409, vertices_689, vertices_481, vertices_590, vertices_326, vertices_738, vertices_354, vertices_284, vertices_540, vertices_460, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_70, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_28, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_324, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_392, vertices_656, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_551), (false, vertices_789), (false, vertices_409), (false, vertices_689), (false, vertices_481), (true, vertices_70), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_324), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 14 else
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 5 6 8 4 738 578 2
cert_row_4 1 1 2 5 8 0 590 76 3
cert_row_4 2 2 5 6 7 1 460 200 3
cert_row_4 3 3 5 6 8 2 728 656 1
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 738
cert_cover_5 2 0 0 4 5 6 98 738 3
cert_coverFacet 3 354
cert_cover_2 3 4 0 5 7 98 354 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 460
cert_cover_5 6 2 1 2 5 6 76 460 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 152 728 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_103

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/P0_104.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_104

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 267, 675, 291, 421, 457, 721, 302, 558, 780, 692, 468, 788, 856, 11, 35, 259, 515, 73, 265, 161, 289, 193, 577, 385, 641, 46, 266, 522, 290, 546, 268, 524, 148, 276, 532, 164, 292, 548, 388, 772, 328, 584, 776, 208, 336, 592, 656, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_267, vertices_675, vertices_291, vertices_421, vertices_457, vertices_721, vertices_302, vertices_558, vertices_780, vertices_692, vertices_468, vertices_788, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_515, vertices_73, vertices_265, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_46, vertices_266, vertices_522, vertices_290, vertices_546, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_328, vertices_584, vertices_776, vertices_208, vertices_336, vertices_592, vertices_656, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_267), (false, vertices_675), (false, vertices_291), (false, vertices_421), (false, vertices_457), (false, vertices_721), (true, vertices_46), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_776), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_267) then 10 else
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_291) then 11 else
  if p.val = (false, vertices_421) then 13 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (true, vertices_46) then 14 else
  if p.val = (true, vertices_268) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 1 268 0 524 2 148 276 532 548 772 776 336 784 267 291 421 46 587 675 457 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 0 46
cert_row_4 1 1 3 6 8 4 692 148 3
cert_row_4 2 3 5 6 7 1 468 208 3
cert_row_4 3 3 5 7 8 2 856 336 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 780
cert_cover_2 2 2 1 7 8 268 780 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 148 692 2
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 148 468 2
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 328 856 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_104

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/P0_108.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_108

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 135, 707, 357, 389, 457, 625, 398, 782, 650, 820, 376, 728, 792, 7, 131, 515, 37, 133, 261, 97, 545, 193, 321, 577, 385, 270, 134, 518, 138, 522, 642, 292, 548, 388, 772, 88, 280, 536, 200, 328, 392, 648, 776, 112, 304, 560, 592, 784, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_135, vertices_707, vertices_357, vertices_389, vertices_457, vertices_625, vertices_398, vertices_782, vertices_650, vertices_820, vertices_376, vertices_728, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_515, vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_270, vertices_134, vertices_518, vertices_138, vertices_522, vertices_642, vertices_292, vertices_548, vertices_388, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_592, vertices_784, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_135), (false, vertices_707), (false, vertices_357), (false, vertices_389), (false, vertices_457), (false, vertices_625), (true, vertices_270), (true, vertices_138), (true, vertices_522), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 12 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 16 else
  if p.val = (false, vertices_135) then 10 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_389) then 11 else
  if p.val = (false, vertices_457) then 13 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_270) then 14 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 2 138 0 522 1 772 88 280 536 648 776 304 784 135 389 457 270 551 707 357 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 8 6 728 88 3
cert_row_4 1 1 3 4 7 8 820 292 1
cert_row_4 2 2 4 5 7 3 376 328 1
cert_row_2 3 1 2 7 0 270
cert_rows
cert_pivot_2 6 8 3 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 270 398 3
cert_coverFacet 1 782
cert_cover_5 1 3 0 1 2 8 270 782 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 292 820 1
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 88 376 2
cert_coverFacet 5 728
cert_cover_5 5 0 2 3 5 6 88 728 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_108

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/P0_109.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_109

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 295, 227, 341, 361, 721, 902, 170, 298, 906, 660, 788, 856, 744, 7, 35, 131, 21, 261, 81, 145, 97, 289, 193, 321, 134, 262, 42, 138, 266, 162, 290, 898, 148, 276, 532, 644, 772, 104, 168, 296, 328, 584, 648, 776, 336, 592, 656, 784, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_295, vertices_227, vertices_341, vertices_361, vertices_721, vertices_902, vertices_170, vertices_298, vertices_906, vertices_660, vertices_788, vertices_856, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_35, vertices_131, vertices_21, vertices_261, vertices_81, vertices_145, vertices_97, vertices_289, vertices_193, vertices_321, vertices_134, vertices_262, vertices_42, vertices_138, vertices_266, vertices_162, vertices_290, vertices_898, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_328, vertices_584, vertices_648, vertices_776, vertices_336, vertices_592, vertices_656, vertices_784, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_295), (false, vertices_227), (false, vertices_341), (false, vertices_361), (false, vertices_721), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_898), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_168), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 12 else
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_898) then 17 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 5 7 8 3 856 328 3
cert_row_4 1 4 5 6 8 2 744 224 3
cert_row_2 2 6 7 8 0 898
cert_rows_3
cert_pivot_3 2 3 0
cert_heightProof 3
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 134 902 3
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 906
cert_cover_5 3 2 0 2 6 7 138 906 3
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 856
cert_cover_5 6 0 2 3 5 7 328 856 1
cert_coverFacet 7 744
cert_cover_5 7 1 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_109

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/P0_110.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_110

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 331, 787, 547, 557, 77, 905, 242, 562, 466, 460, 652, 740, 944, 35, 67, 259, 515, 13, 37, 69, 73, 265, 521, 545, 769, 50, 210, 274, 530, 98, 546, 322, 76, 140, 524, 100, 548, 196, 644, 328, 392, 648, 176, 560, 400, 784, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_331, vertices_787, vertices_547, vertices_557, vertices_77, vertices_905, vertices_242, vertices_562, vertices_466, vertices_460, vertices_652, vertices_740, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_13, vertices_37, vertices_69, vertices_73, vertices_265, vertices_521, vertices_545, vertices_769, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_76, vertices_140, vertices_524, vertices_100, vertices_548, vertices_196, vertices_644, vertices_328, vertices_392, vertices_648, vertices_176, vertices_560, vertices_400, vertices_784, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_331), (false, vertices_787), (false, vertices_547), (false, vertices_557), (false, vertices_77), (false, vertices_905), (true, vertices_50), (true, vertices_210), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_176), (true, vertices_560), (true, vertices_400), (true, vertices_224), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 12 15 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 13 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_787) then 19 else
  if p.val = (false, vertices_547) then 10 else
  if p.val = (false, vertices_557) then 14 else
  if p.val = (false, vertices_77) then 11 else
  if p.val = (false, vertices_905) then 17 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_210) then 20 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 5 6 7 2 460 196 3
cert_row_4 1 4 5 6 8 1 740 224 3
cert_row_4 2 3 6 7 8 4 944 400 3
cert_row_2 3 3 5 6 0 210
cert_rows
cert_pivot_2 2 1 4 0
cert_heightProof 4
cert_coverFacet 0 242
cert_cover_5 0 3 0 3 4 5 50 242 3
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 466
cert_cover_5 2 3 0 3 5 7 210 466 3
cert_coverFacet 3 460
cert_cover_5 3 0 1 2 5 6 76 460 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 100 740 3
cert_coverFacet 6 944
cert_cover_5 6 2 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_110

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/P0_111.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_111

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 77, 653, 597, 233, 465, 785, 566, 682, 370, 786, 482, 124, 556, 13, 69, 517, 73, 137, 81, 273, 529, 193, 385, 641, 769, 50, 274, 530, 354, 162, 546, 386, 642, 770, 44, 76, 524, 52, 84, 532, 548, 104, 168, 552, 648, 112, 336, 784, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_77, vertices_653, vertices_597, vertices_233, vertices_465, vertices_785, vertices_566, vertices_682, vertices_370, vertices_786, vertices_482, vertices_124, vertices_556] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_73, vertices_137, vertices_81, vertices_273, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_50, vertices_274, vertices_530, vertices_354, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_524, vertices_52, vertices_84, vertices_532, vertices_548, vertices_104, vertices_168, vertices_552, vertices_648, vertices_112, vertices_336, vertices_784, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_77), (false, vertices_653), (false, vertices_597), (false, vertices_233), (false, vertices_465), (false, vertices_785), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_354), (true, vertices_162), (true, vertices_546), (true, vertices_44), (true, vertices_52), (true, vertices_548), (true, vertices_552), (true, vertices_112)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_77) then 10 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_785) then 11 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_354) then 14 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_112) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 50 1 274 2 530 162 546 44 52 548 552 112 77 785 899 354 653 597 233 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 8 6 682 546 1
cert_row_4 1 0 1 3 4 8 566 50 1
cert_row_4 2 2 3 4 5 1 124 104 1
cert_row_2 3 4 5 7 0 354
cert_rows
cert_pivot_2 6 8 1 0
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 50 566 1
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 162 682 1
cert_coverFacet 2 370
cert_cover_5 2 3 0 3 4 5 50 370 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 482
cert_cover_5 4 3 0 4 5 6 354 482 3
cert_coverFacet 5 124
cert_cover_5 5 2 1 2 3 4 44 124 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_111

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/P0_112.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_112

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 789, 617, 369, 689, 206, 590, 406, 774, 482, 684, 660, 232, 432, 49, 273, 529, 97, 545, 321, 577, 769, 78, 134, 262, 518, 194, 322, 578, 386, 770, 140, 524, 148, 276, 532, 644, 772, 104, 168, 552, 200, 584, 176, 304, 400, 656, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_789, vertices_617, vertices_369, vertices_689, vertices_206, vertices_590, vertices_406, vertices_774, vertices_482, vertices_684, vertices_660, vertices_232, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_78, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_644, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_176, vertices_304, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_789), (false, vertices_617), (false, vertices_369), (false, vertices_689), (true, vertices_78), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_644), (true, vertices_168), (true, vertices_200), (true, vertices_400), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_78) then 16 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 3 406 134 3
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 1 2 6 8 4 684 140 3
cert_row_2 3 1 2 5 0 78
cert_rows
cert_pivot_2 3 7 4 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 3 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 3 0 1 2 8 78 590 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 6 134 406 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 194 482 1
cert_coverFacet 5 684
cert_cover_5 5 2 1 2 4 6 140 684 2
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_112

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/P0_113.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_113

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 163, 387, 613, 453, 713, 689, 186, 794, 458, 818, 844, 804, 664, 35, 131, 259, 37, 69, 261, 161, 545, 193, 577, 385, 641, 26, 138, 266, 50, 786, 162, 290, 386, 292, 548, 324, 580, 772, 152, 536, 200, 328, 584, 648, 776, 176, 560, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_163, vertices_387, vertices_613, vertices_453, vertices_713, vertices_689, vertices_186, vertices_794, vertices_458, vertices_818, vertices_844, vertices_804, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_37, vertices_69, vertices_261, vertices_161, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_138, vertices_266, vertices_50, vertices_786, vertices_162, vertices_290, vertices_386, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_176, vertices_560, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_163), (false, vertices_387), (false, vertices_613), (false, vertices_453), (false, vertices_713), (false, vertices_689), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_50), (true, vertices_786), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_328), (true, vertices_776), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_163) then 10 else
  if p.val = (false, vertices_387) then 11 else
  if p.val = (false, vertices_613) then 16 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_786) then 14 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_7 0 26 1 138 2 266 50 772 152 536 328 776 800 163 387 295 786 613 453 713 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 4 186 26 3
cert_row_4 1 0 2 5 7 6 458 266 2
cert_row_4 2 2 5 7 8 1 844 328 3
cert_row_2 3 3 7 8 0 786
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 0 0 2 3 4 26 186 3
cert_coverFacet 1 794
cert_cover_5 1 3 0 2 3 7 26 794 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 138 458 2
cert_coverFacet 3 818
cert_cover_5 3 3 0 3 4 7 50 818 3
cert_coverFacet 4 844
cert_cover_5 4 2 1 2 5 7 324 844 1
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_113

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/P0_114.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_114

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 805, 841, 369, 721, 174, 558, 714, 178, 658, 396, 780, 436, 472, 49, 81, 529, 289, 545, 321, 577, 769, 46, 138, 522, 50, 146, 530, 162, 546, 642, 140, 268, 524, 164, 292, 548, 388, 772, 200, 328, 584, 392, 776, 176, 304, 208, 336, 400, 656, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_805, vertices_841, vertices_369, vertices_721, vertices_174, vertices_558, vertices_714, vertices_178, vertices_658, vertices_396, vertices_780, vertices_436, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_46, vertices_138, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_805), (false, vertices_841), (false, vertices_369), (false, vertices_721), (true, vertices_46), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_388), (true, vertices_200), (true, vertices_392), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_4 1 2 3 6 7 5 472 392 1
cert_row_4 2 1 4 6 7 3 436 164 3
cert_row_2 3 1 2 4 0 46
cert_rows
cert_pivot_2 8 5 3 0
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 3 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 3 0 1 2 8 46 558 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 138 714 2
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 436
cert_cover_5 7 2 1 3 4 6 164 436 1
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 6 200 472 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_114

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/P0_115.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_115

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 709, 601, 457, 785, 929, 110, 590, 678, 538, 298, 818, 484, 360, 25, 73, 265, 273, 529, 193, 577, 385, 641, 769, 78, 38, 518, 26, 42, 266, 522, 274, 530, 290, 546, 100, 164, 196, 580, 644, 536, 104, 296, 328, 584, 784, 352, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_709, vertices_601, vertices_457, vertices_785, vertices_929, vertices_110, vertices_590, vertices_678, vertices_538, vertices_298, vertices_818, vertices_484, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_38, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_536, vertices_104, vertices_296, vertices_328, vertices_584, vertices_784, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_709), (false, vertices_601), (false, vertices_457), (false, vertices_785), (false, vertices_929), (true, vertices_78), (true, vertices_38), (true, vertices_518), (true, vertices_42), (true, vertices_522), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_164), (true, vertices_104), (true, vertices_296), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 14 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_785) then 12 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 7 8 3 818 290 3
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 1 5 6 7 4 484 196 3
cert_row_2 3 1 2 5 0 78
cert_rows
cert_pivot_2 3 8 4 0
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 3 0 1 2 4 78 110 3
cert_coverFacet 1 590
cert_cover_5 1 3 0 1 2 8 78 590 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 818
cert_cover_5 5 0 0 3 4 7 274 818 2
cert_coverFacet 6 484
cert_cover_5 6 2 1 4 5 6 100 484 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_115

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/P0_116.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_116

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 661, 361, 681, 777, 433, 214, 598, 842, 402, 482, 620, 228, 676, 41, 265, 521, 145, 273, 529, 161, 289, 641, 769, 86, 146, 274, 530, 194, 322, 578, 386, 770, 148, 532, 100, 164, 548, 196, 580, 644, 104, 552, 328, 584, 776, 400, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_661, vertices_361, vertices_681, vertices_777, vertices_433, vertices_214, vertices_598, vertices_842, vertices_402, vertices_482, vertices_620, vertices_228, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_769, vertices_86, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_661), (false, vertices_361), (false, vertices_681), (false, vertices_777), (false, vertices_433), (true, vertices_86), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_584), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_777) then 12 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_86) then 15 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 146 194 322 578 386 100 164 548 196 580 584 224 777 787 86 661 361 681 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 7 6 482 322 1
cert_row_4 1 0 2 5 8 7 842 578 1
cert_row_4 2 1 4 5 8 2 620 100 3
cert_row_2 3 1 3 5 0 86
cert_rows
cert_pivot_2 6 7 2 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 3 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 3 0 1 3 8 86 598 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 322 842 1
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 482
cert_cover_5 4 0 0 4 5 6 194 482 1
cert_coverFacet 5 620
cert_cover_5 5 2 1 2 4 5 100 620 1
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_116

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/P0_117.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_117

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 901, 345, 617, 777, 481, 118, 534, 422, 646, 602, 610, 796, 372, 73, 265, 521, 97, 161, 545, 321, 385, 641, 769, 22, 38, 134, 518, 82, 530, 98, 162, 546, 578, 642, 116, 276, 532, 292, 388, 644, 772, 88, 280, 536, 584, 776, 336, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_901, vertices_345, vertices_617, vertices_777, vertices_481, vertices_118, vertices_534, vertices_422, vertices_646, vertices_602, vertices_610, vertices_796, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_134, vertices_518, vertices_82, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_116, vertices_276, vertices_532, vertices_292, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_584, vertices_776, vertices_336, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_901), (false, vertices_345), (false, vertices_617), (false, vertices_777), (false, vertices_481), (true, vertices_22), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_578), (true, vertices_116), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_536)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_777) then 12 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_116) then 17 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_536) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 0 0 1 4 7 6 422 38 3
cert_row_4 1 2 3 5 8 0 602 88 3
cert_row_4 2 1 3 7 8 2 796 276 3
cert_row_2 3 3 4 5 1 116
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 3 0 1 3 4 22 118 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 38 422 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 602
cert_cover_5 4 1 0 2 3 5 82 602 1
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 796
cert_cover_5 6 2 1 2 3 7 276 796 1
cert_coverFacet 7 372
cert_cover_5 7 3 1 3 4 7 116 372 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_117

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/P0_118.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_118

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 597, 405, 357, 457, 705, 310, 566, 810, 714, 394, 402, 620, 360, 21, 69, 261, 145, 529, 193, 321, 577, 385, 641, 54, 138, 266, 522, 146, 274, 530, 290, 546, 386, 642, 276, 532, 100, 292, 548, 580, 104, 296, 552, 200, 328, 584, 392, 400, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_597, vertices_405, vertices_357, vertices_457, vertices_705, vertices_310, vertices_566, vertices_810, vertices_714, vertices_394, vertices_402, vertices_620, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_400, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_597), (false, vertices_405), (false, vertices_357), (false, vertices_457), (false, vertices_705), (true, vertices_54), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_548), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_705) then 12 else
  if p.val = (true, vertices_54) then 15 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_584) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 138 266 522 274 290 546 386 548 104 296 552 584 705 659 54 597 405 357 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 8 7 810 522 2
cert_row_4 1 0 2 5 8 6 714 522 2
cert_row_4 2 1 4 5 8 2 620 100 3
cert_row_2 3 1 3 4 0 54
cert_rows
cert_pivot_2 7 6 2 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 3 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 3 0 1 3 8 54 566 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 7 266 810 2
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 138 714 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 620
cert_cover_5 6 2 1 2 4 5 100 620 1
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_118

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/P0_119.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_119

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 205, 597, 149, 185, 313, 841, 662, 178, 306, 866, 674, 740, 488, 21, 69, 133, 57, 73, 137, 265, 145, 273, 529, 577, 769, 50, 146, 274, 530, 162, 290, 546, 642, 770, 148, 532, 196, 580, 644, 168, 296, 200, 328, 176, 304, 224, 352, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_205, vertices_597, vertices_149, vertices_185, vertices_313, vertices_841, vertices_662, vertices_178, vertices_306, vertices_866, vertices_674, vertices_740, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_133, vertices_57, vertices_73, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_577, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_168, vertices_296, vertices_200, vertices_328, vertices_176, vertices_304, vertices_224, vertices_352, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_205), (false, vertices_597), (false, vertices_149), (false, vertices_185), (false, vertices_313), (false, vertices_841), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_644), (true, vertices_224), (true, vertices_352), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 13 else
  if p.val = (false, vertices_205) then 15 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_149) then 11 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 8 3 662 642 1
cert_row_4 1 4 5 7 8 0 866 352 3
cert_row_4 2 4 5 6 8 1 740 224 3
cert_row_4 3 4 5 6 7 2 488 224 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 866
cert_cover_5 3 1 0 4 5 7 290 866 2
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 196 740 1
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 168 488 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_119

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/P0_120.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_120

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 659, 611, 229, 681, 465, 838, 794, 812, 612, 420, 452, 440, 664, 19, 67, 515, 337, 145, 97, 161, 545, 193, 641, 274, 530, 322, 578, 770, 100, 164, 292, 548, 196, 324, 580, 388, 772, 152, 280, 536, 168, 296, 552, 648, 776, 400, 656, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_659, vertices_611, vertices_229, vertices_681, vertices_465, vertices_838, vertices_794, vertices_812, vertices_612, vertices_420, vertices_452, vertices_440, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_515, vertices_337, vertices_145, vertices_97, vertices_161, vertices_545, vertices_193, vertices_641, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_400, vertices_656, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_659), (false, vertices_611), (false, vertices_229), (false, vertices_681), (false, vertices_465), (true, vertices_770), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_776), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 21 else
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 7 8 5 838 770 1
cert_row_4 1 2 3 7 8 0 794 280 3
cert_row_4 2 2 4 7 8 1 812 296 3
cert_row_4 3 3 4 6 7 2 440 400 1
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 292 812 1
cert_coverFacet 3 612
cert_cover_2 3 4 1 5 8 100 612 3
cert_coverFacet 4 420
cert_cover_2 4 4 1 6 7 164 420 3
cert_coverFacet 5 452
cert_cover_2 5 5 1 6 7 196 452 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 152 440 2
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_120

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/P0_123.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_123

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 653, 597, 421, 325, 241, 657, 398, 682, 842, 626, 418, 844, 688, 69, 133, 261, 517, 81, 145, 529, 97, 161, 289, 321, 641, 138, 266, 522, 98, 162, 290, 546, 322, 578, 386, 140, 268, 524, 324, 580, 388, 840, 648, 112, 176, 560, 592, 656, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_653, vertices_597, vertices_421, vertices_325, vertices_241, vertices_657, vertices_398, vertices_682, vertices_842, vertices_626, vertices_418, vertices_844, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_289, vertices_321, vertices_641, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_386, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_388, vertices_840, vertices_648, vertices_112, vertices_176, vertices_560, vertices_592, vertices_656, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_653), (false, vertices_597), (false, vertices_421), (false, vertices_325), (false, vertices_241), (false, vertices_657), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_578), (true, vertices_386), (true, vertices_268), (true, vertices_840), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 13 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_325) then 10 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_657) then 11 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_840) then 19 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_840), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 1 398 138 3
cert_row_4 1 0 2 4 8 6 682 522 2
cert_row_4 2 3 4 5 8 0 626 112 3
cert_row_2 3 5 7 8 2 840
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 138 682 2
cert_coverFacet 2 842
cert_cover_5 2 3 0 2 5 7 266 842 2
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 98 626 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 844
cert_cover_5 5 3 1 2 5 7 268 844 2
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_123

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/P0_124.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_124

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 611, 899, 837, 425, 369, 654, 570, 348, 540, 396, 628, 900, 312, 35, 131, 515, 169, 97, 289, 321, 577, 385, 769, 42, 138, 522, 546, 642, 28, 140, 268, 524, 84, 532, 324, 580, 388, 644, 772, 56, 280, 536, 296, 392, 112, 304, 560, 336, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_611, vertices_899, vertices_837, vertices_425, vertices_369, vertices_654, vertices_570, vertices_348, vertices_540, vertices_396, vertices_628, vertices_900, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_169, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_769, vertices_42, vertices_138, vertices_522, vertices_546, vertices_642, vertices_28, vertices_140, vertices_268, vertices_524, vertices_84, vertices_532, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_536, vertices_296, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_611), (false, vertices_899), (false, vertices_837), (false, vertices_425), (false, vertices_369), (true, vertices_522), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 19 else
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 8 6 654 522 1
cert_row_4 1 2 3 4 8 0 570 56 3
cert_row_4 2 1 3 5 7 2 348 84 3
cert_row_4 3 3 4 5 8 1 628 112 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 42 570 2
cert_coverFacet 2 348
cert_cover_5 2 2 1 2 3 5 28 348 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 84 628 2
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_124

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/P0_125.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_125

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 659, 451, 837, 793, 737, 302, 154, 170, 418, 620, 780, 484, 696, 19, 131, 259, 281, 529, 193, 321, 577, 641, 769, 26, 42, 138, 266, 146, 162, 290, 386, 44, 268, 524, 100, 292, 324, 580, 772, 152, 536, 168, 552, 776, 656, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_659, vertices_451, vertices_837, vertices_793, vertices_737, vertices_302, vertices_154, vertices_170, vertices_418, vertices_620, vertices_780, vertices_484, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_281, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_146, vertices_162, vertices_290, vertices_386, vertices_44, vertices_268, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_776, vertices_656, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_659), (false, vertices_451), (false, vertices_837), (false, vertices_793), (false, vertices_737), (true, vertices_42), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_292), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 19 else
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 7 0 302 44 3
cert_row_4 1 1 4 5 6 7 484 100 3
cert_row_4 2 2 4 5 8 1 620 552 2
cert_row_4 3 3 4 6 8 2 696 656 1
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 42 302 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 620
cert_cover_5 4 2 1 2 4 5 44 620 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 484
cert_cover_5 6 1 1 4 5 6 100 484 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 152 696 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_125

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/P0_126.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_126

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 835, 805, 569, 345, 433, 654, 422, 774, 218, 450, 692, 664, 464, 579, 25, 73, 521, 49, 273, 289, 545, 321, 769, 134, 262, 518, 74, 138, 522, 194, 322, 386, 770, 164, 292, 548, 644, 772, 88, 152, 536, 648, 176, 560, 208, 336, 400, 656, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_835, vertices_805, vertices_569, vertices_345, vertices_433, vertices_654, vertices_422, vertices_774, vertices_218, vertices_450, vertices_692, vertices_664, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_579, vertices_25, vertices_73, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_769, vertices_134, vertices_262, vertices_518, vertices_74, vertices_138, vertices_522, vertices_194, vertices_322, vertices_386, vertices_770, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_152, vertices_536, vertices_648, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_835), (false, vertices_805), (false, vertices_569), (false, vertices_345), (false, vertices_433), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_648), (true, vertices_208), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 1 4 6 7 422 134 2
cert_row_4 1 0 2 3 6 5 218 138 2
cert_row_4 2 1 2 6 8 0 654 644 1
cert_row_4 3 3 4 6 8 1 692 176 3
cert_rows
cert_pivot_2 7 5 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 134 654 2
cert_coverFacet 1 422
cert_cover_5 1 0 0 1 4 6 134 422 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 218
cert_cover_5 3 1 0 2 3 5 74 218 2
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 164 692 1
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_126

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/P0_127.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_127

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 837, 809, 457, 721, 62, 598, 806, 154, 554, 658, 316, 468, 408, 137, 265, 521, 193, 321, 577, 641, 769, 22, 38, 518, 26, 42, 138, 522, 146, 530, 546, 642, 60, 84, 276, 292, 324, 580, 772, 152, 280, 296, 552, 392, 208, 592, 400, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_837, vertices_809, vertices_457, vertices_721, vertices_62, vertices_598, vertices_806, vertices_154, vertices_554, vertices_658, vertices_316, vertices_468, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_26, vertices_42, vertices_138, vertices_522, vertices_146, vertices_530, vertices_546, vertices_642, vertices_60, vertices_84, vertices_276, vertices_292, vertices_324, vertices_580, vertices_772, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_208, vertices_592, vertices_400, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_837), (false, vertices_809), (false, vertices_457), (false, vertices_721), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_60), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_152), (true, vertices_280), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_60) then 18 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 1 3 5 7 6 468 84 3
cert_row_4 1 0 1 3 8 5 598 22 3
cert_row_4 2 1 4 7 8 0 806 292 3
cert_row_2 3 2 3 4 1 60
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 3 0 1 2 3 22 62 2
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 7 38 806 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 7 60 316 3
cert_coverFacet 7 468
cert_cover_5 7 0 1 3 5 6 84 468 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_127

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/P0_128.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_128

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 659, 611, 709, 425, 401, 225, 790, 802, 412, 236, 844, 660, 872, 19, 35, 515, 145, 273, 97, 161, 289, 193, 577, 385, 641, 274, 530, 290, 546, 770, 76, 140, 268, 148, 276, 532, 196, 580, 644, 772, 104, 168, 296, 840, 392, 400, 656, 224, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_659, vertices_611, vertices_709, vertices_425, vertices_401, vertices_225, vertices_790, vertices_802, vertices_412, vertices_236, vertices_844, vertices_660, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_76, vertices_140, vertices_268, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_840, vertices_392, vertices_400, vertices_656, vertices_224, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_659), (false, vertices_611), (false, vertices_709), (false, vertices_425), (false, vertices_401), (false, vertices_225), (true, vertices_770), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_104), (true, vertices_840), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 13 else
  if p.val = (false, vertices_659) then 14 else
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_401) then 10 else
  if p.val = (false, vertices_225) then 11 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_840) then 20 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_840), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 7 8 0 790 276 3
cert_row_4 1 1 2 6 7 3 412 140 3
cert_row_4 2 2 4 5 6 1 236 104 3
cert_row_2 3 5 7 8 2 840
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 802
cert_cover_2 1 4 0 7 8 290 802 3
cert_coverFacet 2 412
cert_cover_5 2 1 1 2 3 6 140 412 2
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 76 236 2
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 76 844 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 872
cert_cover_5 6 3 2 4 5 7 104 872 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_128

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/P0_129.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_129

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 661, 837, 601, 209, 481, 678, 774, 570, 362, 842, 418, 248, 688, 133, 261, 517, 81, 145, 529, 193, 321, 577, 385, 134, 262, 518, 42, 330, 522, 162, 290, 546, 386, 770, 644, 772, 56, 88, 536, 104, 584, 176, 560, 208, 656, 224, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_661, vertices_837, vertices_601, vertices_209, vertices_481, vertices_678, vertices_774, vertices_570, vertices_362, vertices_842, vertices_418, vertices_248, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_134, vertices_262, vertices_518, vertices_42, vertices_330, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_584, vertices_176, vertices_560, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_661), (false, vertices_837), (false, vertices_601), (false, vertices_209), (false, vertices_481), (true, vertices_518), (true, vertices_42), (true, vertices_330), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_56), (true, vertices_104), (true, vertices_176), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_209) then 12 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_330) then 15 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row_4 0 0 4 6 8 1 678 162 3
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 2 4 5 6 3 248 104 3
cert_row_2 3 2 5 7 0 330
cert_rows
cert_pivot_2 1 8 3 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 134 678 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 362
cert_cover_5 3 3 0 2 4 5 42 362 3
cert_coverFacet 4 842
cert_cover_5 4 3 0 2 5 8 330 842 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 56 248 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_129

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/P0_133.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_133

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [47, 75, 227, 333, 165, 901, 849, 705, 314, 346, 178, 722, 428, 944, 11, 35, 67, 13, 37, 133, 261, 73, 161, 193, 321, 577, 641, 769, 282, 42, 74, 50, 82, 146, 162, 194, 44, 268, 164, 388, 296, 328, 176, 304, 336, 592, 656, 784, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_47, vertices_75, vertices_227, vertices_333, vertices_165, vertices_901, vertices_849, vertices_705, vertices_314, vertices_346, vertices_178, vertices_722, vertices_428, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_67, vertices_13, vertices_37, vertices_133, vertices_261, vertices_73, vertices_161, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_282, vertices_42, vertices_74, vertices_50, vertices_82, vertices_146, vertices_162, vertices_194, vertices_44, vertices_268, vertices_164, vertices_388, vertices_296, vertices_328, vertices_176, vertices_304, vertices_336, vertices_592, vertices_656, vertices_784, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_47), (false, vertices_75), (false, vertices_227), (false, vertices_333), (false, vertices_165), (false, vertices_901), (false, vertices_849), (false, vertices_705), (true, vertices_282), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_47) then 12 else
  if p.val = (false, vertices_75) then 8 else
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_333) then 13 else
  if p.val = (false, vertices_165) then 9 else
  if p.val = (false, vertices_901) then 14 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (false, vertices_705) then 10 else
  if p.val = (true, vertices_282) then 17 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_416) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_47), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 8 5 722 146 3
cert_row_4 1 2 4 6 7 1 428 296 2
cert_row_4 2 3 6 7 8 4 944 656 2
cert_row_2 3 2 3 7 0 282
cert_rows
cert_pivot_2 5 1 4 0
cert_heightProof 4
cert_coverFacet 0 314
cert_cover_5 0 3 0 2 3 4 282 314 3
cert_coverFacet 1 346
cert_cover_5 1 3 0 2 3 5 282 346 3
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 722
cert_cover_5 3 0 0 3 5 6 82 722 3
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 44 428 3
cert_coverFacet 5 944
cert_cover_5 5 2 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_133

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/P0_134.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_134

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 613, 425, 713, 817, 225, 206, 590, 566, 150, 410, 786, 436, 228, 137, 265, 521, 97, 161, 289, 545, 193, 577, 769, 78, 22, 134, 518, 138, 266, 522, 146, 274, 530, 770, 52, 148, 100, 164, 548, 196, 580, 200, 584, 392, 304, 560, 400, 784, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_613, vertices_425, vertices_713, vertices_817, vertices_225, vertices_206, vertices_590, vertices_566, vertices_150, vertices_410, vertices_786, vertices_436, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_78, vertices_22, vertices_134, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_52, vertices_148, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_200, vertices_584, vertices_392, vertices_304, vertices_560, vertices_400, vertices_784, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_613), (false, vertices_425), (false, vertices_713), (false, vertices_817), (false, vertices_225), (true, vertices_78), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_52), (true, vertices_148), (true, vertices_164), (true, vertices_196), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_225) then 12 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_400) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 22 134 518 138 146 274 530 52 148 164 196 400 225 779 78 613 425 713 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 22 3
cert_row_4 1 1 3 6 7 4 436 148 3
cert_row_4 2 0 2 6 7 3 410 138 3
cert_row_2 3 1 2 5 0 78
cert_rows
cert_pivot_2 8 4 3 0
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 3 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 3 0 1 2 8 78 590 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 22 566 3
cert_coverFacet 3 150
cert_cover_2 3 1 0 3 6 22 150 3
cert_coverFacet 4 410
cert_cover_5 4 2 0 2 3 6 138 410 2
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 436
cert_cover_5 6 1 1 3 4 6 52 436 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_134

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/P0_135.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_135

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 837, 793, 617, 201, 465, 174, 558, 790, 454, 538, 402, 740, 232, 25, 73, 137, 521, 145, 273, 193, 321, 577, 769, 46, 134, 262, 518, 26, 138, 522, 146, 274, 530, 386, 164, 548, 196, 324, 580, 772, 536, 104, 168, 552, 200, 400, 784, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_837, vertices_793, vertices_617, vertices_201, vertices_465, vertices_174, vertices_558, vertices_790, vertices_454, vertices_538, vertices_402, vertices_740, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_521, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_772, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_837), (false, vertices_793), (false, vertices_617), (false, vertices_201), (false, vertices_465), (true, vertices_46), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_168), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_201) then 12 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 134 262 518 522 274 530 386 164 548 196 168 224 201 155 46 837 793 617 465
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
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 740
cert_cover_5 6 2 1 4 5 6 164 740 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_135

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/P0_139.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_139

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 597, 405, 805, 425, 177, 838, 186, 218, 362, 594, 802, 460, 212, 21, 261, 517, 49, 145, 529, 161, 289, 545, 385, 154, 42, 74, 50, 82, 530, 290, 546, 322, 578, 770, 84, 148, 196, 324, 580, 388, 772, 168, 296, 200, 328, 392, 176, 208, 592, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_597, vertices_405, vertices_805, vertices_425, vertices_177, vertices_838, vertices_186, vertices_218, vertices_362, vertices_594, vertices_802, vertices_460, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_385, vertices_154, vertices_42, vertices_74, vertices_50, vertices_82, vertices_530, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_208, vertices_592, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_597), (false, vertices_405), (false, vertices_805), (false, vertices_425), (false, vertices_177), (true, vertices_154), (true, vertices_42), (true, vertices_74), (true, vertices_82), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_196), (true, vertices_324), (true, vertices_200), (true, vertices_328), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_177) then 12 else
  if p.val = (true, vertices_154) then 15 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_208) then 11 else
  0
cert_priority
cert_nodeAtPriority_57 42 74 82 290 322 578 770 196 324 200 328 208 177 563 154 597 405 805 425
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_4 1 0 2 5 7 4 362 74 3
cert_row_4 2 2 5 6 7 1 460 200 3
cert_row_2 3 2 3 6 0 154
cert_rows
cert_pivot_2 8 4 1 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 186
cert_cover_5 1 3 0 2 3 4 154 186 3
cert_coverFacet 2 218
cert_cover_5 2 3 0 2 3 5 154 218 3
cert_coverFacet 3 362
cert_cover_5 3 1 0 2 4 5 42 362 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 460
cert_cover_5 6 2 1 2 5 6 196 460 1
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_139

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/P0_140.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_140

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 115, 787, 227, 781, 341, 197, 682, 562, 428, 652, 452, 824, 496, 19, 99, 131, 515, 69, 133, 261, 517, 81, 273, 193, 769, 50, 530, 162, 546, 642, 140, 268, 524, 196, 324, 388, 644, 168, 296, 552, 648, 776, 112, 304, 560, 336, 784, 224, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_115, vertices_787, vertices_227, vertices_781, vertices_341, vertices_197, vertices_682, vertices_562, vertices_428, vertices_652, vertices_452, vertices_824, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_99, vertices_131, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_273, vertices_193, vertices_769, vertices_50, vertices_530, vertices_162, vertices_546, vertices_642, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_388, vertices_644, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_224, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_115), (false, vertices_787), (false, vertices_227), (false, vertices_781), (false, vertices_341), (false, vertices_197), (true, vertices_546), (true, vertices_140), (true, vertices_388), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_560), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_115) then 18 else
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_197) then 11 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_388) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 6 8 0 682 168 3
cert_row_4 1 2 4 6 7 1 428 168 3
cert_row_4 2 3 4 7 8 2 824 304 3
cert_row_4 3 4 5 6 7 3 496 224 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 162 682 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 428
cert_cover_5 2 1 1 2 4 6 140 428 2
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 296 824 1
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_140

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/P0_141.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_141

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 661, 229, 805, 713, 353, 790, 602, 282, 362, 412, 428, 664, 232, 37, 133, 517, 97, 289, 193, 321, 577, 641, 769, 26, 74, 266, 274, 530, 322, 578, 770, 396, 148, 276, 532, 164, 292, 772, 152, 280, 536, 104, 168, 296, 200, 584, 648, 656, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_661, vertices_229, vertices_805, vertices_713, vertices_353, vertices_790, vertices_602, vertices_282, vertices_362, vertices_412, vertices_428, vertices_664, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_26, vertices_74, vertices_266, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_396, vertices_148, vertices_276, vertices_532, vertices_164, vertices_292, vertices_772, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_200, vertices_584, vertices_648, vertices_656, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_661), (false, vertices_229), (false, vertices_805), (false, vertices_713), (false, vertices_353), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_396), (true, vertices_276), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 18 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_713) then 16 else
  if p.val = (false, vertices_353) then 12 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 4 362 74 3
cert_row_4 1 0 2 3 8 5 602 26 3
cert_row_4 2 1 3 7 8 0 790 276 3
cert_row_2 3 2 6 7 1 396
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 26 602 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 74 362 2
cert_coverFacet 4 412
cert_cover_5 4 3 1 2 3 6 396 412 2
cert_coverFacet 5 428
cert_cover_5 5 3 1 2 4 6 396 428 2
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_141

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/P0_142.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_142

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 597, 185, 89, 617, 913, 790, 358, 614, 418, 898, 348, 408, 488, 25, 41, 73, 81, 145, 529, 161, 545, 577, 641, 102, 262, 518, 162, 290, 546, 386, 642, 770, 84, 276, 532, 324, 580, 88, 152, 280, 104, 168, 328, 392, 400, 784, 352, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_597, vertices_185, vertices_89, vertices_617, vertices_913, vertices_790, vertices_358, vertices_614, vertices_418, vertices_898, vertices_348, vertices_408, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_81, vertices_145, vertices_529, vertices_161, vertices_545, vertices_577, vertices_641, vertices_102, vertices_262, vertices_518, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_328, vertices_392, vertices_400, vertices_784, vertices_352, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_597), (false, vertices_185), (false, vertices_89), (false, vertices_617), (false, vertices_913), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_276), (true, vertices_324), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_89) then 12 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
cert_nodeAtPriority_56 262 518 290 386 770 276 324 280 328 392 352 416 89 675 102 597 185 617 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 262 2
cert_row_4 1 1 2 5 7 3 348 324 1
cert_row_4 2 4 5 6 7 2 488 352 2
cert_row_2 3 1 4 5 0 102
cert_rows
cert_pivot_2 8 3 2 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 262 790 2
cert_coverFacet 1 358
cert_cover_5 1 3 0 1 4 7 102 358 3
cert_coverFacet 2 614
cert_cover_5 2 3 0 1 4 8 102 614 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 348
cert_cover_5 5 1 1 2 3 5 84 348 1
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 488
cert_cover_5 7 2 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_142

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/P0_144.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_144

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 779, 595, 387, 397, 525, 613, 818, 466, 236, 556, 936, 496, 624, 67, 131, 259, 515, 13, 69, 133, 517, 265, 521, 577, 385, 82, 274, 530, 194, 386, 770, 44, 140, 524, 100, 548, 196, 168, 552, 392, 776, 112, 304, 560, 464, 592, 224, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_779, vertices_595, vertices_387, vertices_397, vertices_525, vertices_613, vertices_818, vertices_466, vertices_236, vertices_556, vertices_936, vertices_496, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_13, vertices_69, vertices_133, vertices_517, vertices_265, vertices_521, vertices_577, vertices_385, vertices_82, vertices_274, vertices_530, vertices_194, vertices_386, vertices_770, vertices_44, vertices_140, vertices_524, vertices_100, vertices_548, vertices_196, vertices_168, vertices_552, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_464, vertices_592, vertices_224, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_779), (false, vertices_595), (false, vertices_387), (false, vertices_397), (false, vertices_525), (false, vertices_613), (true, vertices_274), (true, vertices_44), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_464), (true, vertices_224), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_387) then 10 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_525) then 11 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_464) then 21 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
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
cert_row_4 0 3 4 7 8 0 818 304 3
cert_row_4 1 2 4 5 6 1 236 168 2
cert_row_4 2 4 6 7 8 2 936 416 3
cert_row_2 3 5 6 7 3 464
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 818
cert_cover_5 0 0 0 3 4 7 274 818 2
cert_coverFacet 1 466
cert_cover_5 1 3 0 3 5 6 82 466 3
cert_coverFacet 2 236
cert_cover_5 2 1 1 2 4 5 44 236 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 936
cert_cover_5 4 2 2 4 6 7 168 936 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_144

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2073 : Certifies 2073 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_103.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2074 : Certifies 2074 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_104.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2075 : Certifies 2075 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_108.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2076 : Certifies 2076 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_109.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2077 : Certifies 2077 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_110.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2078 : Certifies 2078 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_111.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2079 : Certifies 2079 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_112.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2080 : Certifies 2080 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_113.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2081 : Certifies 2081 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_114.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2082 : Certifies 2082 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_115.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2083 : Certifies 2083 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_116.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2084 : Certifies 2084 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_117.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2085 : Certifies 2085 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_118.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2086 : Certifies 2086 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_119.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2087 : Certifies 2087 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_120.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2088 : Certifies 2088 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_123.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2089 : Certifies 2089 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_124.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2090 : Certifies 2090 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_125.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2091 : Certifies 2091 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_126.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2092 : Certifies 2092 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_127.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2093 : Certifies 2093 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_128.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2094 : Certifies 2094 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_129.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2095 : Certifies 2095 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_133.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2096 : Certifies 2096 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_134.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2097 : Certifies 2097 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_135.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2098 : Certifies 2098 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_139.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2099 : Certifies 2099 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_140.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2100 : Certifies 2100 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_141.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2101 : Certifies 2101 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_142.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2102 : Certifies 2102 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_144.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B068 (j : Fin 30) :
    Certifies (2073 + j.val) := by
  fin_cases j
  · exact projection_2073
  · exact projection_2074
  · exact projection_2075
  · exact projection_2076
  · exact projection_2077
  · exact projection_2078
  · exact projection_2079
  · exact projection_2080
  · exact projection_2081
  · exact projection_2082
  · exact projection_2083
  · exact projection_2084
  · exact projection_2085
  · exact projection_2086
  · exact projection_2087
  · exact projection_2088
  · exact projection_2089
  · exact projection_2090
  · exact projection_2091
  · exact projection_2092
  · exact projection_2093
  · exact projection_2094
  · exact projection_2095
  · exact projection_2096
  · exact projection_2097
  · exact projection_2098
  · exact projection_2099
  · exact projection_2100
  · exact projection_2101
  · exact projection_2102

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
