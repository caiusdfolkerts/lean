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
/- Source: ProjectionCertificates/R_m15e10q1_0363.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0363

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 327, 789, 905, 721, 481, 62, 270, 426, 626, 354, 540, 780, 568, 744, 71, 21, 261, 81, 529, 193, 321, 385, 641, 769, 14, 22, 262, 42, 266, 50, 82, 98, 290, 322, 28, 268, 524, 532, 772, 56, 536, 168, 552, 392, 648, 776, 560, 592, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_327, vertices_789, vertices_905, vertices_721, vertices_481, vertices_62, vertices_270, vertices_426, vertices_626, vertices_354, vertices_540, vertices_780, vertices_568, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_21, vertices_261, vertices_81, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_42, vertices_266, vertices_50, vertices_82, vertices_98, vertices_290, vertices_322, vertices_28, vertices_268, vertices_524, vertices_532, vertices_772, vertices_56, vertices_536, vertices_168, vertices_552, vertices_392, vertices_648, vertices_776, vertices_560, vertices_592, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_327), (false, vertices_789), (false, vertices_905), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_98), (true, vertices_290), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_56), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_560), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 16 else
  if p.val = (false, vertices_327) then 17 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 62 14 3
cert_row_4 1 0 2 4 6 7 426 42 3
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 426
cert_cover_5 2 1 0 2 4 6 42 426 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 50 626 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 168 744 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0363

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0364.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0364

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 519, 803, 661, 681, 241, 305, 334, 590, 778, 372, 596, 728, 488, 808, 7, 259, 515, 21, 517, 49, 145, 273, 161, 289, 545, 641, 78, 262, 518, 266, 522, 770, 84, 276, 532, 324, 580, 168, 296, 552, 200, 328, 584, 648, 776, 112, 304, 208, 592, 656, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_519, vertices_803, vertices_661, vertices_681, vertices_241, vertices_305, vertices_334, vertices_590, vertices_778, vertices_372, vertices_596, vertices_728, vertices_488, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_259, vertices_515, vertices_21, vertices_517, vertices_49, vertices_145, vertices_273, vertices_161, vertices_289, vertices_545, vertices_641, vertices_78, vertices_262, vertices_518, vertices_266, vertices_522, vertices_770, vertices_84, vertices_276, vertices_532, vertices_324, vertices_580, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_519), (false, vertices_803), (false, vertices_661), (false, vertices_681), (false, vertices_241), (false, vertices_305), (true, vertices_78), (true, vertices_266), (true, vertices_522), (true, vertices_84), (true, vertices_324), (true, vertices_580), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 519 305 266 522 84 324 580 296 200 328 584 776 592 352 279 803 78 661 681 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 1 3 4 5 7 372 84 2
cert_row_4 2 2 3 5 6 8 728 200 1
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 84 372 2
cert_coverFacet 4 596
cert_cover_2 4 3 1 5 8 84 596 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 200 728 1
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 168 488 2
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0364

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0366.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0366

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 589, 809, 457, 689, 705, 94, 182, 710, 346, 306, 450, 796, 660, 816, 73, 265, 521, 161, 289, 545, 193, 577, 385, 641, 22, 70, 134, 90, 50, 274, 162, 290, 194, 322, 386, 28, 76, 524, 148, 532, 580, 644, 280, 328, 776, 176, 304, 560, 656, 784, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_589, vertices_809, vertices_457, vertices_689, vertices_705, vertices_94, vertices_182, vertices_710, vertices_346, vertices_306, vertices_450, vertices_796, vertices_660, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_22, vertices_70, vertices_134, vertices_90, vertices_50, vertices_274, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_76, vertices_524, vertices_148, vertices_532, vertices_580, vertices_644, vertices_280, vertices_328, vertices_776, vertices_176, vertices_304, vertices_560, vertices_656, vertices_784, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_589), (false, vertices_809), (false, vertices_457), (false, vertices_689), (false, vertices_705), (true, vertices_22), (true, vertices_70), (true, vertices_134), (true, vertices_90), (true, vertices_50), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_28), (true, vertices_148), (true, vertices_532), (true, vertices_644), (true, vertices_280), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 705 22 70 134 50 274 194 322 28 148 532 644 280 304 784 419 90 589 809 457 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 22 3
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_2 2 0 2 3 5 90
cert_row_4 3 1 2 3 7 8 796 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 3 22 94 2
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 4 22 182 3
cert_coverFacet 2 710
cert_cover_5 2 1 0 1 5 6 70 710 3
cert_coverFacet 3 346
cert_cover_5 3 2 0 2 3 7 90 346 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 28 796 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0366

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0367.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0367

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 327, 789, 905, 721, 481, 30, 270, 58, 426, 626, 354, 572, 780, 744, 71, 21, 261, 81, 529, 193, 321, 385, 641, 769, 14, 22, 262, 26, 42, 266, 50, 82, 98, 290, 322, 28, 268, 524, 532, 772, 56, 168, 552, 392, 648, 776, 560, 592, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_327, vertices_789, vertices_905, vertices_721, vertices_481, vertices_30, vertices_270, vertices_58, vertices_426, vertices_626, vertices_354, vertices_572, vertices_780, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_21, vertices_261, vertices_81, vertices_529, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_26, vertices_42, vertices_266, vertices_50, vertices_82, vertices_98, vertices_290, vertices_322, vertices_28, vertices_268, vertices_524, vertices_532, vertices_772, vertices_56, vertices_168, vertices_552, vertices_392, vertices_648, vertices_776, vertices_560, vertices_592, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_327), (false, vertices_789), (false, vertices_905), (false, vertices_721), (false, vertices_481), (true, vertices_14), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_98), (true, vertices_290), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_56), (true, vertices_168), (true, vertices_552), (true, vertices_560), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 16 else
  if p.val = (false, vertices_327) then 17 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 1 2 3 4 8 572 28 3
cert_row_4 3 2 4 5 6 8 744 168 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 426
cert_cover_5 3 0 0 2 4 6 42 426 3
cert_coverFacet 4 626
cert_cover_5 4 1 0 3 4 5 50 626 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 572
cert_cover_5 6 2 1 2 3 4 28 572 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 168 744 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0367

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0368.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0368

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 93, 341, 569, 841, 433, 206, 422, 326, 690, 706, 834, 668, 404, 712, 85, 25, 73, 521, 49, 273, 289, 545, 321, 769, 70, 134, 262, 162, 290, 546, 194, 322, 578, 642, 770, 28, 76, 140, 148, 276, 324, 388, 536, 200, 584, 648, 176, 560, 400, 656, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_93, vertices_341, vertices_569, vertices_841, vertices_433, vertices_206, vertices_422, vertices_326, vertices_690, vertices_706, vertices_834, vertices_668, vertices_404, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_25, vertices_73, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_769, vertices_70, vertices_134, vertices_262, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_76, vertices_140, vertices_148, vertices_276, vertices_324, vertices_388, vertices_536, vertices_200, vertices_584, vertices_648, vertices_176, vertices_560, vertices_400, vertices_656, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_93), (false, vertices_341), (false, vertices_569), (false, vertices_841), (false, vertices_433), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_162), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_140), (true, vertices_148), (true, vertices_388), (true, vertices_200), (true, vertices_648), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 70 1 134 2 262 162 194 322 578 642 140 148 388 200 648 656 704 803 93 341 569 841 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 70 2
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 3 4 6 8 690 162 1
cert_row_4 3 1 2 3 6 8 668 28 3
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 70 206 2
cert_coverFacet 1 422
cert_cover_5 1 1 0 1 4 6 134 422 2
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 690
cert_cover_5 3 2 0 3 4 6 162 690 1
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 28 668 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0368

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0369.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0369

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 653, 805, 453, 849, 62, 218, 682, 818, 594, 284, 556, 396, 308, 472, 133, 261, 517, 193, 321, 577, 641, 769, 26, 42, 138, 50, 82, 530, 546, 194, 578, 642, 28, 44, 140, 268, 524, 52, 276, 292, 548, 388, 216, 280, 552, 392, 648, 304, 336, 592, 784, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_653, vertices_805, vertices_453, vertices_849, vertices_62, vertices_218, vertices_682, vertices_818, vertices_594, vertices_284, vertices_556, vertices_396, vertices_308, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_50, vertices_82, vertices_530, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_140, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_388, vertices_216, vertices_280, vertices_552, vertices_392, vertices_648, vertices_304, vertices_336, vertices_592, vertices_784, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_653), (false, vertices_805), (false, vertices_453), (false, vertices_849), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_216), (true, vertices_280), (true, vertices_552), (true, vertices_392), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_216) then 23 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_304) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 2 3 4 62 26 1
cert_row_4 2 0 2 4 6 8 682 42 3
cert_row_4 3 0 3 4 7 8 818 50 3
cert_rows
cert_pivot_2 5 1 2 0
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 3 26 62 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 682
cert_cover_5 2 2 0 2 4 6 42 682 3
cert_coverFacet 3 818
cert_cover_5 3 3 0 3 4 7 50 818 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coverFacet 9 472
cert_cover_5 9 0 2 3 5 7 216 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0369

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0370.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0370

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 275, 387, 565, 793, 617, 425, 214, 342, 458, 844, 180, 788, 740, 232, 19, 131, 259, 41, 265, 521, 49, 273, 529, 161, 545, 385, 86, 146, 274, 194, 322, 386, 52, 148, 276, 532, 164, 548, 196, 324, 580, 772, 104, 168, 200, 328, 584, 392, 776, 176, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_275, vertices_387, vertices_565, vertices_793, vertices_617, vertices_425, vertices_214, vertices_342, vertices_458, vertices_844, vertices_180, vertices_788, vertices_740, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_41, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_86, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_275), (false, vertices_387), (false, vertices_565), (false, vertices_793), (false, vertices_617), (false, vertices_425), (true, vertices_86), (true, vertices_194), (true, vertices_322), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_200), (true, vertices_328), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 15 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (true, vertices_86) then 16 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 1 2 5 7 8 844 324 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 194 458 1
cert_coverFacet 3 844
cert_cover_5 3 2 1 2 5 7 324 844 1
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0370

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0372.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0372

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 565, 793, 329, 369, 737, 286, 542, 422, 710, 202, 394, 308, 676, 488, 73, 265, 521, 49, 273, 529, 97, 545, 321, 577, 30, 134, 262, 518, 74, 138, 266, 522, 194, 578, 386, 52, 276, 532, 164, 292, 548, 644, 280, 536, 200, 328, 392, 304, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_565, vertices_793, vertices_329, vertices_369, vertices_737, vertices_286, vertices_542, vertices_422, vertices_710, vertices_202, vertices_394, vertices_308, vertices_676, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_30, vertices_134, vertices_262, vertices_518, vertices_74, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_304, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_565), (false, vertices_793), (false, vertices_329), (false, vertices_369), (false, vertices_737), (true, vertices_30), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_644), (true, vertices_200), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_30) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 329 134 262 518 138 266 194 386 276 164 292 644 200 392 416 587 30 565 793 369 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 1 5 6 8 710 134 2
cert_row_4 2 0 1 4 6 7 422 134 2
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 3 8 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 7 30 286 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 422
cert_cover_5 2 2 0 1 4 6 134 422 2
cert_coverFacet 3 710
cert_cover_5 3 1 0 1 5 6 134 710 2
cert_coverFacet 4 202
cert_cover_2 4 2 0 5 6 74 202 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 200 488 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0372

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0373.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0373

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 677, 453, 617, 849, 225, 174, 558, 406, 602, 154, 786, 120, 184, 496, 133, 261, 517, 97, 161, 545, 193, 321, 577, 769, 46, 134, 262, 518, 26, 138, 522, 146, 274, 530, 770, 164, 548, 388, 56, 88, 152, 104, 168, 552, 584, 112, 176, 336, 592, 400, 784, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_677, vertices_453, vertices_617, vertices_849, vertices_225, vertices_174, vertices_558, vertices_406, vertices_602, vertices_154, vertices_786, vertices_120, vertices_184, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_164, vertices_548, vertices_388, vertices_56, vertices_88, vertices_152, vertices_104, vertices_168, vertices_552, vertices_584, vertices_112, vertices_176, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_677), (false, vertices_453), (false, vertices_617), (false, vertices_849), (false, vertices_225), (true, vertices_46), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_168), (true, vertices_112), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 225 134 26 138 522 146 274 530 56 88 152 168 112 176 400 775 46 677 453 617 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 0 1 2 4 46
cert_row_4 2 0 1 3 6 7 406 134 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 2 0 3
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 1 0 1 2 8 46 558 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 134 406 2
cert_coverFacet 3 602
cert_cover_5 3 0 0 2 3 5 26 602 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0373

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0374.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0374

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 333, 409, 201, 721, 865, 158, 174, 278, 358, 690, 802, 284, 108, 744, 73, 137, 265, 145, 273, 529, 193, 321, 577, 769, 142, 22, 38, 262, 146, 274, 530, 162, 290, 546, 770, 28, 44, 76, 268, 276, 100, 324, 152, 280, 104, 168, 200, 656, 352, 608, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_333, vertices_409, vertices_201, vertices_721, vertices_865, vertices_158, vertices_174, vertices_278, vertices_358, vertices_690, vertices_802, vertices_284, vertices_108, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_142, vertices_22, vertices_38, vertices_262, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_276, vertices_100, vertices_324, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_656, vertices_352, vertices_608, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_333), (false, vertices_409), (false, vertices_201), (false, vertices_721), (false, vertices_865), (true, vertices_142), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_276), (true, vertices_100), (true, vertices_104), (true, vertices_168), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 201 22 38 262 146 162 290 546 28 44 276 100 104 168 672 787 142 333 409 721 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 7 358 38 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 1 0 1 2 4 142 174 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 358
cert_cover_5 3 0 0 1 4 5 38 358 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 146 690 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 108
cert_cover_2 7 2 1 4 5 44 108 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0374

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0375.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0375

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 805, 681, 241, 305, 849, 286, 558, 838, 346, 202, 650, 188, 308, 216, 49, 81, 273, 161, 289, 545, 193, 577, 641, 769, 14, 262, 518, 282, 74, 138, 522, 194, 322, 578, 642, 28, 44, 52, 276, 292, 548, 772, 88, 152, 168, 552, 200, 648, 176, 304, 208, 336, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_805, vertices_681, vertices_241, vertices_305, vertices_849, vertices_286, vertices_558, vertices_838, vertices_346, vertices_202, vertices_650, vertices_188, vertices_308, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_262, vertices_518, vertices_282, vertices_74, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_28, vertices_44, vertices_52, vertices_276, vertices_292, vertices_548, vertices_772, vertices_88, vertices_152, vertices_168, vertices_552, vertices_200, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_805), (false, vertices_681), (false, vertices_241), (false, vertices_305), (false, vertices_849), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_282), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_322), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_276), (true, vertices_88), (true, vertices_152), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_282) then 17 else
  if p.val = (true, vertices_74) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_200) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 305 14 262 518 74 138 522 322 28 44 52 276 88 152 200 707 282 805 681 241 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 262 2
cert_row_2 1 0 2 3 7 282
cert_row_4 2 0 1 2 4 8 558 14 3
cert_row_4 3 1 2 3 4 6 188 28 3
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 558
cert_cover_5 1 2 0 1 2 4 14 558 3
cert_coverFacet 2 838
cert_cover_5 2 0 0 1 5 7 262 838 2
cert_coverFacet 3 346
cert_cover_5 3 1 0 2 3 5 282 346 3
cert_coverFacet 4 202
cert_cover_2 4 2 0 5 6 74 202 3
cert_coverFacet 5 650
cert_cover_2 5 2 0 6 8 138 650 3
cert_coverFacet 6 188
cert_cover_5 6 3 1 2 3 4 28 188 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0375

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0376.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0376

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 397, 837, 217, 585, 481, 158, 182, 294, 774, 570, 866, 420, 600, 752, 13, 261, 517, 73, 137, 521, 193, 321, 577, 385, 14, 150, 38, 262, 518, 26, 522, 50, 290, 546, 770, 140, 164, 292, 388, 772, 88, 152, 536, 584, 176, 560, 208, 592, 224, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_397, vertices_837, vertices_217, vertices_585, vertices_481, vertices_158, vertices_182, vertices_294, vertices_774, vertices_570, vertices_866, vertices_420, vertices_600, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_193, vertices_321, vertices_577, vertices_385, vertices_14, vertices_150, vertices_38, vertices_262, vertices_518, vertices_26, vertices_522, vertices_50, vertices_290, vertices_546, vertices_770, vertices_140, vertices_164, vertices_292, vertices_388, vertices_772, vertices_88, vertices_152, vertices_536, vertices_584, vertices_176, vertices_560, vertices_208, vertices_592, vertices_224, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_397), (false, vertices_837), (false, vertices_217), (false, vertices_585), (false, vertices_481), (true, vertices_150), (true, vertices_38), (true, vertices_262), (true, vertices_26), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_164), (true, vertices_292), (true, vertices_536), (true, vertices_176), (true, vertices_560), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_150) then 17 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 585 38 262 26 50 290 546 770 164 292 536 176 560 592 608 527 150 397 837 217 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 4 150 182 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 570
cert_cover_5 4 1 0 2 3 4 26 570 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 290 866 2
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 176 752 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0376

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0377.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0377

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 805, 105, 425, 713, 625, 566, 278, 774, 346, 458, 722, 124, 284, 300, 41, 73, 137, 97, 289, 545, 577, 385, 641, 769, 22, 262, 518, 330, 82, 274, 530, 194, 386, 642, 770, 28, 44, 268, 52, 276, 292, 548, 772, 88, 280, 104, 296, 200, 392, 112, 560, 592, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_805, vertices_105, vertices_425, vertices_713, vertices_625, vertices_566, vertices_278, vertices_774, vertices_346, vertices_458, vertices_722, vertices_124, vertices_284, vertices_300] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_137, vertices_97, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_262, vertices_518, vertices_330, vertices_82, vertices_274, vertices_530, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_805), (false, vertices_105), (false, vertices_425), (false, vertices_713), (false, vertices_625), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_330), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_276), (true, vertices_88), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_330) then 17 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_280) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 105 22 262 518 82 274 530 194 28 44 268 52 276 88 280 899 330 805 425 713 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 7 330
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 2 3 4 5 124 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 22 566 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 346
cert_cover_5 3 0 0 2 3 5 330 346 2
cert_coverFacet 4 458
cert_cover_5 4 0 0 2 5 6 330 458 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 6 82 722 3
cert_coverFacet 6 124
cert_cover_5 6 3 1 2 3 4 28 124 3
cert_coverFacet 7 284
cert_cover_2 7 2 1 3 7 28 284 3
cert_coverFacet 8 300
cert_cover_2 8 2 1 4 7 44 300 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0377

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0378.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0378

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 229, 549, 837, 809, 433, 710, 314, 538, 842, 402, 658, 188, 668, 556, 37, 69, 517, 161, 289, 545, 193, 321, 385, 769, 26, 266, 522, 146, 274, 530, 194, 322, 578, 386, 642, 156, 44, 524, 164, 548, 196, 580, 644, 56, 536, 296, 552, 776, 176, 304, 400, 656, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_229, vertices_549, vertices_837, vertices_809, vertices_433, vertices_710, vertices_314, vertices_538, vertices_842, vertices_402, vertices_658, vertices_188, vertices_668, vertices_556] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_156, vertices_44, vertices_524, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_536, vertices_296, vertices_552, vertices_776, vertices_176, vertices_304, vertices_400, vertices_656, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_229), (false, vertices_549), (false, vertices_837), (false, vertices_809), (false, vertices_433), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_642), (true, vertices_156), (true, vertices_44), (true, vertices_524), (true, vertices_644), (true, vertices_56), (true, vertices_536), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_156) then 20 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 0 2 5 7 8 842 266 2
cert_rows
cert_pivot_2 4 3 1 0
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 26 314 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 842
cert_cover_5 3 3 0 2 5 7 266 842 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 188
cert_cover_5 6 1 1 2 3 4 156 188 3
cert_coverFacet 7 668
cert_cover_5 7 1 1 2 3 8 156 668 3
cert_coverFacet 8 556
cert_cover_2 8 2 1 4 8 44 556 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0378

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0379.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0379

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 541, 309, 613, 793, 481, 158, 282, 650, 778, 466, 738, 684, 180, 432, 21, 37, 517, 537, 273, 97, 289, 321, 577, 769, 26, 138, 266, 522, 146, 274, 194, 322, 578, 642, 770, 28, 140, 524, 52, 148, 164, 548, 280, 648, 776, 176, 304, 400, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_541, vertices_309, vertices_613, vertices_793, vertices_481, vertices_158, vertices_282, vertices_650, vertices_778, vertices_466, vertices_738, vertices_684, vertices_180, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_537, vertices_273, vertices_97, vertices_289, vertices_321, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_148, vertices_164, vertices_548, vertices_280, vertices_648, vertices_776, vertices_176, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_541), (false, vertices_309), (false, vertices_613), (false, vertices_793), (false, vertices_481), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_148), (true, vertices_164), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 146 2
cert_row_4 1 0 1 2 3 6 158 26 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 26 158 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 6 146 466 2
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 194 738 1
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 180
cert_cover_2 7 3 1 4 6 52 180 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0379

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0380.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0380

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 613, 165, 453, 425, 817, 710, 314, 538, 458, 650, 786, 188, 668, 564, 37, 69, 133, 161, 289, 545, 321, 577, 385, 769, 26, 138, 266, 522, 274, 530, 194, 322, 578, 642, 770, 156, 52, 532, 164, 548, 196, 580, 644, 56, 536, 168, 296, 392, 648, 304, 560, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_613, vertices_165, vertices_453, vertices_425, vertices_817, vertices_710, vertices_314, vertices_538, vertices_458, vertices_650, vertices_786, vertices_188, vertices_668, vertices_564] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_156, vertices_52, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_536, vertices_168, vertices_296, vertices_392, vertices_648, vertices_304, vertices_560, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_613), (false, vertices_165), (false, vertices_453), (false, vertices_425), (false, vertices_817), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_156), (true, vertices_52), (true, vertices_532), (true, vertices_644), (true, vertices_56), (true, vertices_536), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_156) then 20 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 0 2 5 6 7 458 138 2
cert_rows
cert_pivot_2 8 1 3 0
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 314
cert_cover_5 1 2 0 2 3 4 26 314 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 458
cert_cover_5 3 3 0 2 5 6 138 458 2
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 188
cert_cover_5 6 1 1 2 3 4 156 188 3
cert_coverFacet 7 668
cert_cover_5 7 1 1 2 3 8 156 668 3
cert_coverFacet 8 564
cert_cover_2 8 3 1 4 8 52 564 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0380

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0381.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0381

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 837, 793, 369, 177, 737, 542, 398, 710, 58, 426, 178, 780, 484, 312, 49, 145, 273, 529, 97, 161, 321, 577, 641, 769, 14, 134, 518, 26, 42, 394, 50, 146, 530, 162, 642, 268, 524, 196, 324, 580, 388, 772, 56, 280, 536, 296, 776, 176, 304, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_837, vertices_793, vertices_369, vertices_177, vertices_737, vertices_542, vertices_398, vertices_710, vertices_58, vertices_426, vertices_178, vertices_780, vertices_484, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_134, vertices_518, vertices_26, vertices_42, vertices_394, vertices_50, vertices_146, vertices_530, vertices_162, vertices_642, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_280, vertices_536, vertices_296, vertices_776, vertices_176, vertices_304, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_837), (false, vertices_793), (false, vertices_369), (false, vertices_177), (false, vertices_737), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_394), (true, vertices_50), (true, vertices_162), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_388), (true, vertices_56), (true, vertices_296), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_394) then 17 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 177 14 134 518 26 42 50 162 268 524 196 388 56 296 416 659 394 837 793 369 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 398
cert_cover_5 1 1 0 1 2 6 14 398 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 58
cert_cover_2 3 2 0 3 4 26 58 3
cert_coverFacet 4 426
cert_cover_5 4 1 0 2 4 6 42 426 3
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 196 484 1
cert_coverFacet 8 312
cert_cover_2 8 3 2 4 7 56 312 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0381

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0382.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0382

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 115, 275, 675, 901, 337, 481, 286, 58, 554, 604, 780, 468, 740, 632, 19, 35, 259, 515, 81, 273, 97, 161, 321, 385, 641, 769, 26, 42, 266, 522, 50, 274, 546, 28, 268, 524, 84, 276, 196, 580, 388, 644, 772, 56, 600, 552, 776, 112, 336, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_115, vertices_275, vertices_675, vertices_901, vertices_337, vertices_481, vertices_286, vertices_58, vertices_554, vertices_604, vertices_780, vertices_468, vertices_740, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_81, vertices_273, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_546, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_600, vertices_552, vertices_776, vertices_112, vertices_336, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_115), (false, vertices_275), (false, vertices_675), (false, vertices_901), (false, vertices_337), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_580), (true, vertices_56), (true, vertices_600), (true, vertices_552), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_675) then 17 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_600) then 21 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_2 1 2 3 5 8 600
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 604
cert_cover_5 3 1 1 2 3 5 28 604 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 84 468 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 196 740 1
cert_coverFacet 7 632
cert_cover_5 7 1 2 3 4 5 56 632 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0382

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0383.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0383

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 397, 233, 809, 465, 609, 782, 342, 534, 242, 562, 610, 188, 572, 404, 41, 137, 265, 97, 545, 193, 321, 577, 385, 769, 22, 262, 518, 50, 82, 530, 98, 546, 322, 578, 770, 60, 140, 268, 524, 148, 276, 532, 388, 168, 552, 776, 176, 560, 208, 336, 400, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_397, vertices_233, vertices_809, vertices_465, vertices_609, vertices_782, vertices_342, vertices_534, vertices_242, vertices_562, vertices_610, vertices_188, vertices_572, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_262, vertices_518, vertices_50, vertices_82, vertices_530, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_60, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_168, vertices_552, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_397), (false, vertices_233), (false, vertices_809), (false, vertices_465), (false, vertices_609), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_60), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_176), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 609 2 22 1 262 3 518 50 82 530 98 546 524 148 276 532 176 560 835 397 60 233 809 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 3 5 7 342 22 3
cert_row_4 3 0 3 4 5 6 242 50 3
cert_rows
cert_pivot_2 8 2 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 342
cert_cover_5 1 2 0 1 3 5 22 342 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 242
cert_cover_5 3 3 0 3 4 5 50 242 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 188
cert_cover_5 6 1 1 2 3 6 60 188 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0383

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0384.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0384

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 613, 601, 233, 297, 817, 398, 214, 598, 806, 154, 786, 484, 216, 424, 25, 41, 73, 265, 273, 529, 97, 289, 545, 577, 86, 134, 262, 518, 26, 138, 266, 146, 274, 530, 770, 100, 292, 548, 196, 580, 388, 88, 152, 168, 296, 200, 392, 208, 592, 784, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_613, vertices_601, vertices_233, vertices_297, vertices_817, vertices_398, vertices_214, vertices_598, vertices_806, vertices_154, vertices_786, vertices_484, vertices_216, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_265, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_86, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_770, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_392, vertices_208, vertices_592, vertices_784, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_613), (false, vertices_601), (false, vertices_233), (false, vertices_297), (false, vertices_817), (true, vertices_86), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_770), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 297 134 262 518 138 146 530 770 292 196 388 152 392 208 416 283 86 613 601 233 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 1 2 6 7 398 134 2
cert_row_4 2 0 1 4 7 8 806 262 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 214
cert_cover_5 1 0 0 1 3 6 86 214 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 8 86 598 3
cert_coverFacet 3 806
cert_cover_5 3 2 0 1 4 7 262 806 2
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 100 484 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0384

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0385.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0385

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 613, 121, 153, 713, 817, 790, 710, 390, 314, 154, 394, 236, 428, 804, 25, 73, 137, 49, 145, 529, 97, 545, 577, 641, 134, 262, 518, 26, 138, 266, 146, 274, 530, 386, 642, 172, 100, 292, 548, 196, 580, 388, 772, 56, 152, 104, 296, 200, 392, 304, 784, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_613, vertices_121, vertices_153, vertices_713, vertices_817, vertices_790, vertices_710, vertices_390, vertices_314, vertices_154, vertices_394, vertices_236, vertices_428, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_49, vertices_145, vertices_529, vertices_97, vertices_545, vertices_577, vertices_641, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_172, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_152, vertices_104, vertices_296, vertices_200, vertices_392, vertices_304, vertices_784, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_613), (false, vertices_121), (false, vertices_153), (false, vertices_713), (false, vertices_817), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_274), (true, vertices_386), (true, vertices_172), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_772), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_172) then 19 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 153 2 134 1 262 3 518 26 138 266 274 386 292 196 388 772 296 392 659 613 172 121 713 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 134 2
cert_row_2 1 1 2 4 6 172
cert_row_4 2 0 1 3 7 8 790 262 2
cert_row_4 3 0 2 3 4 7 314 26 3
cert_rows
cert_pivot_2 5 6 1 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 262 790 2
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 134 710 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 314
cert_cover_5 3 3 0 2 3 4 26 314 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 236
cert_cover_5 6 1 1 2 4 5 172 236 3
cert_coverFacet 7 428
cert_cover_5 7 1 1 2 4 7 172 428 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0385

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0386.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0386

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 93, 525, 229, 805, 537, 721, 782, 666, 282, 242, 370, 802, 364, 344, 13, 37, 69, 517, 25, 521, 81, 529, 161, 545, 193, 641, 26, 266, 522, 114, 146, 274, 162, 290, 546, 642, 770, 76, 268, 524, 100, 292, 772, 88, 280, 536, 328, 208, 336, 656, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_525, vertices_229, vertices_805, vertices_537, vertices_721, vertices_782, vertices_666, vertices_282, vertices_242, vertices_370, vertices_802, vertices_364, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_25, vertices_521, vertices_81, vertices_529, vertices_161, vertices_545, vertices_193, vertices_641, vertices_26, vertices_266, vertices_522, vertices_114, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_772, vertices_88, vertices_280, vertices_536, vertices_328, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_525), (false, vertices_229), (false, vertices_805), (false, vertices_537), (false, vertices_721), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_114), (true, vertices_146), (true, vertices_274), (true, vertices_290), (true, vertices_770), (true, vertices_268), (true, vertices_280), (true, vertices_328), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 525 1 537 26 266 522 146 274 290 770 268 280 328 336 352 675 114 93 229 805 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 26 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 4 5 7 364 76 2
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
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 76 364 2
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0386

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0387.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0387

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 213, 789, 581, 841, 481, 662, 678, 570, 282, 362, 418, 620, 228, 792, 21, 69, 517, 145, 273, 193, 321, 577, 385, 769, 646, 26, 42, 266, 146, 274, 530, 162, 290, 546, 386, 148, 532, 100, 164, 548, 196, 580, 280, 536, 104, 552, 328, 584, 776, 784, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_213, vertices_789, vertices_581, vertices_841, vertices_481, vertices_662, vertices_678, vertices_570, vertices_282, vertices_362, vertices_418, vertices_620, vertices_228, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_646, vertices_26, vertices_42, vertices_266, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_784, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_213), (false, vertices_789), (false, vertices_581), (false, vertices_841), (false, vertices_481), (true, vertices_646), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_646) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_552) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 581 26 42 266 530 162 290 546 100 164 548 280 536 104 552 403 646 213 789 841 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 646 662 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 646 678 2
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 26 570 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 362
cert_cover_5 4 2 0 2 4 5 42 362 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 100 620 1
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0387

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0388.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0388

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 139, 659, 301, 333, 565, 85, 217, 806, 170, 418, 962, 724, 836, 488, 11, 131, 515, 269, 21, 37, 69, 41, 73, 137, 81, 145, 529, 545, 42, 138, 162, 290, 546, 386, 642, 770, 84, 532, 292, 548, 324, 580, 772, 168, 296, 200, 328, 208, 656, 416, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_139, vertices_659, vertices_301, vertices_333, vertices_565, vertices_85, vertices_217, vertices_806, vertices_170, vertices_418, vertices_962, vertices_724, vertices_836, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_515, vertices_269, vertices_21, vertices_37, vertices_69, vertices_41, vertices_73, vertices_137, vertices_81, vertices_145, vertices_529, vertices_545, vertices_42, vertices_138, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_208, vertices_656, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_139), (false, vertices_659), (false, vertices_301), (false, vertices_333), (false, vertices_565), (false, vertices_85), (false, vertices_217), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_580), (true, vertices_772), (true, vertices_168), (true, vertices_416), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 8 724 84 3
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 386 962 1
cert_coverFacet 4 724
cert_cover_5 4 0 1 3 5 6 84 724 3
cert_coverFacet 5 836
cert_cover_2 5 5 1 7 8 324 836 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 168 488 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0388

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0389.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0389

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 661, 613, 421, 793, 801, 206, 654, 346, 538, 658, 482, 588, 228, 872, 37, 133, 517, 145, 273, 529, 289, 545, 385, 769, 142, 26, 74, 522, 146, 274, 530, 194, 322, 386, 642, 76, 524, 100, 164, 196, 580, 644, 280, 536, 328, 584, 776, 656, 224, 352, 608, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_661, vertices_613, vertices_421, vertices_793, vertices_801, vertices_206, vertices_654, vertices_346, vertices_538, vertices_658, vertices_482, vertices_588, vertices_228, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_385, vertices_769, vertices_142, vertices_26, vertices_74, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_76, vertices_524, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_280, vertices_536, vertices_328, vertices_584, vertices_776, vertices_656, vertices_224, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_661), (false, vertices_613), (false, vertices_421), (false, vertices_793), (false, vertices_801), (true, vertices_142), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_76), (true, vertices_524), (true, vertices_196), (true, vertices_328), (true, vertices_584), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_793) then 23 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 801 26 74 522 530 194 322 642 76 524 196 328 584 224 352 403 142 661 613 421 793
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 2 3 5 7 346 26 3
cert_row_4 2 0 4 5 6 7 482 194 1
cert_row_4 3 2 4 5 7 8 872 328 1
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 142 206 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 346
cert_cover_5 2 1 0 2 3 5 26 346 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 482
cert_cover_5 5 2 0 4 5 6 194 482 1
cert_coverFacet 6 588
cert_cover_2 6 2 1 5 8 76 588 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 328 872 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0389

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0390.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0390

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 709, 345, 665, 201, 865, 174, 662, 614, 426, 402, 802, 364, 204, 408, 25, 73, 137, 273, 529, 193, 321, 577, 641, 769, 38, 134, 518, 170, 146, 274, 530, 290, 546, 386, 770, 44, 76, 140, 100, 196, 580, 644, 152, 280, 296, 200, 328, 392, 400, 656, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_709, vertices_345, vertices_665, vertices_201, vertices_865, vertices_174, vertices_662, vertices_614, vertices_426, vertices_402, vertices_802, vertices_364, vertices_204, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_38, vertices_134, vertices_518, vertices_170, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_770, vertices_44, vertices_76, vertices_140, vertices_100, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_296, vertices_200, vertices_328, vertices_392, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_709), (false, vertices_345), (false, vertices_665), (false, vertices_201), (false, vertices_865), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_170), (true, vertices_146), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_100), (true, vertices_296), (true, vertices_392), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_170) then 17 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 201 38 134 518 146 290 546 386 44 76 140 100 296 392 400 787 170 709 345 665 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_2 1 0 2 4 6 170
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 38 174 2
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 6 134 662 2
cert_coverFacet 2 614
cert_cover_5 2 2 0 1 4 5 38 614 3
cert_coverFacet 3 426
cert_cover_5 3 1 0 2 4 7 170 426 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 44 364 3
cert_coverFacet 7 204
cert_cover_2 7 2 1 5 6 76 204 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0390

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0391.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0391

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 213, 713, 689, 337, 865, 286, 526, 182, 678, 842, 802, 460, 652, 340, 49, 81, 145, 273, 289, 545, 193, 321, 577, 641, 14, 22, 166, 518, 266, 522, 50, 274, 290, 546, 770, 140, 268, 524, 84, 148, 276, 196, 324, 644, 200, 328, 584, 648, 176, 336, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_213, vertices_713, vertices_689, vertices_337, vertices_865, vertices_286, vertices_526, vertices_182, vertices_678, vertices_842, vertices_802, vertices_460, vertices_652, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_145, vertices_273, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_22, vertices_166, vertices_518, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_644, vertices_200, vertices_328, vertices_584, vertices_648, vertices_176, vertices_336, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_213), (false, vertices_713), (false, vertices_689), (false, vertices_337), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_166), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_324), (true, vertices_644), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_166) then 17 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 337 14 22 518 266 522 546 770 140 268 524 276 324 644 328 307 166 213 713 689 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 6 166
cert_row_4 1 0 1 2 3 7 286 14 3
cert_row_4 2 0 2 5 7 8 842 266 2
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 182
cert_cover_5 2 0 0 1 3 4 22 182 3
cert_coverFacet 3 678
cert_cover_5 3 0 0 1 4 8 166 678 3
cert_coverFacet 4 842
cert_cover_5 4 2 0 2 5 7 266 842 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 140 460 2
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0391

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0392.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0392

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 275, 675, 387, 405, 617, 241, 902, 842, 338, 124, 348, 812, 180, 676, 19, 131, 259, 515, 81, 145, 273, 97, 161, 545, 577, 385, 82, 274, 322, 578, 386, 642, 770, 92, 44, 268, 52, 148, 276, 164, 548, 388, 644, 772, 104, 552, 328, 584, 776, 112, 176, 336, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_275, vertices_675, vertices_387, vertices_405, vertices_617, vertices_241, vertices_902, vertices_842, vertices_338, vertices_124, vertices_348, vertices_812, vertices_180, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_545, vertices_577, vertices_385, vertices_82, vertices_274, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_92, vertices_44, vertices_268, vertices_52, vertices_148, vertices_276, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_336, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_275), (false, vertices_675), (false, vertices_387), (false, vertices_405), (false, vertices_617), (false, vertices_241), (true, vertices_322), (true, vertices_770), (true, vertices_92), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_328), (true, vertices_776), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_92) then 19 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 275 387 322 770 44 268 52 164 548 644 772 328 776 336 595 675 405 92 617 241
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
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 4 92 124 3
cert_coverFacet 4 348
cert_cover_5 4 0 1 2 3 7 92 348 3
cert_coverFacet 5 812
cert_cover_5 5 3 1 2 4 7 44 812 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0392

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0393.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0393

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 157, 781, 281, 689, 849, 422, 838, 362, 626, 674, 428, 120, 184, 344, 13, 133, 517, 25, 265, 145, 273, 529, 641, 769, 134, 262, 518, 98, 162, 290, 546, 322, 578, 642, 140, 268, 420, 772, 56, 88, 152, 280, 104, 168, 296, 328, 112, 176, 560, 336, 592, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_157, vertices_781, vertices_281, vertices_689, vertices_849, vertices_422, vertices_838, vertices_362, vertices_626, vertices_674, vertices_428, vertices_120, vertices_184, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_265, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_134, vertices_262, vertices_518, vertices_98, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_642, vertices_140, vertices_268, vertices_420, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_328, vertices_112, vertices_176, vertices_560, vertices_336, vertices_592, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_157), (false, vertices_781), (false, vertices_281), (false, vertices_689), (false, vertices_849), (true, vertices_262), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_420), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_112)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_420) then 20 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_112) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
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
cert_row_2 0 1 4 6 7 420
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_4 2 0 2 4 5 7 362 98 1
cert_row_4 3 0 3 4 5 8 626 98 1
cert_rows
cert_pivot_2 6 1 2 0
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 134 422 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 262 838 2
cert_coverFacet 2 362
cert_cover_5 2 2 0 2 4 5 98 362 1
cert_coverFacet 3 626
cert_cover_5 3 3 0 3 4 5 98 626 1
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 428
cert_cover_5 5 0 1 2 4 6 140 428 2
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0393

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0394.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0394

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 589, 805, 453, 601, 369, 398, 154, 538, 810, 242, 418, 220, 780, 480, 69, 261, 517, 585, 49, 81, 529, 289, 545, 321, 26, 138, 266, 522, 50, 146, 530, 162, 290, 546, 386, 76, 140, 268, 524, 196, 388, 772, 88, 152, 536, 776, 112, 208, 224, 352, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_589, vertices_805, vertices_453, vertices_601, vertices_369, vertices_398, vertices_154, vertices_538, vertices_810, vertices_242, vertices_418, vertices_220, vertices_780, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_585, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_388, vertices_772, vertices_88, vertices_152, vertices_536, vertices_776, vertices_112, vertices_208, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_589), (false, vertices_805), (false, vertices_453), (false, vertices_601), (false, vertices_369), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_140), (true, vertices_268), (true, vertices_152), (true, vertices_776), (true, vertices_208), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 1 138 2 266 522 146 162 290 386 140 268 152 776 208 224 416 563 805 453 589 601 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_4 1 0 1 2 6 7 398 138 1
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 2 3 5 6 220 76 2
cert_rows
cert_pivot_2 8 7 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 138 398 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 810
cert_cover_5 3 0 0 2 4 7 266 810 2
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 50 242 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 76 220 2
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0394

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2973 : Certifies 2973 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0363.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2974 : Certifies 2974 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0364.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2975 : Certifies 2975 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0366.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2976 : Certifies 2976 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0367.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2977 : Certifies 2977 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0368.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2978 : Certifies 2978 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0369.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2979 : Certifies 2979 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0370.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2980 : Certifies 2980 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0372.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2981 : Certifies 2981 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0373.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2982 : Certifies 2982 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0374.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2983 : Certifies 2983 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0375.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2984 : Certifies 2984 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0376.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2985 : Certifies 2985 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0377.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2986 : Certifies 2986 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0378.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2987 : Certifies 2987 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0379.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2988 : Certifies 2988 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0380.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2989 : Certifies 2989 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0381.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2990 : Certifies 2990 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0382.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2991 : Certifies 2991 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0383.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2992 : Certifies 2992 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0384.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2993 : Certifies 2993 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0385.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2994 : Certifies 2994 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0386.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2995 : Certifies 2995 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0387.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2996 : Certifies 2996 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0388.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2997 : Certifies 2997 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0389.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2998 : Certifies 2998 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0390.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2999 : Certifies 2999 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0391.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3000 : Certifies 3000 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0392.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3001 : Certifies 3001 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0393.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3002 : Certifies 3002 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0394.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B098 (j : Fin 30) :
    Certifies (2973 + j.val) := by
  fin_cases j
  · exact projection_2973
  · exact projection_2974
  · exact projection_2975
  · exact projection_2976
  · exact projection_2977
  · exact projection_2978
  · exact projection_2979
  · exact projection_2980
  · exact projection_2981
  · exact projection_2982
  · exact projection_2983
  · exact projection_2984
  · exact projection_2985
  · exact projection_2986
  · exact projection_2987
  · exact projection_2988
  · exact projection_2989
  · exact projection_2990
  · exact projection_2991
  · exact projection_2992
  · exact projection_2993
  · exact projection_2994
  · exact projection_2995
  · exact projection_2996
  · exact projection_2997
  · exact projection_2998
  · exact projection_2999
  · exact projection_3000
  · exact projection_3001
  · exact projection_3002

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
