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
/- Source: ProjectionCertificates/R_m15e11q2_0008.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0008

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 355, 707, 653, 213, 341, 570, 794, 306, 610, 188, 284, 780, 744, 496, 67, 259, 515, 85, 133, 261, 517, 193, 321, 641, 538, 50, 274, 98, 290, 546, 578, 770, 28, 140, 268, 524, 148, 276, 772, 56, 280, 168, 552, 648, 776, 176, 304, 208, 336, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_355, vertices_707, vertices_653, vertices_213, vertices_341, vertices_570, vertices_794, vertices_306, vertices_610, vertices_188, vertices_284, vertices_780, vertices_744, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_85, vertices_133, vertices_261, vertices_517, vertices_193, vertices_321, vertices_641, vertices_538, vertices_50, vertices_274, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_772, vertices_56, vertices_280, vertices_168, vertices_552, vertices_648, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_355), (false, vertices_707), (false, vertices_653), (false, vertices_213), (false, vertices_341), (true, vertices_538), (true, vertices_50), (true, vertices_274), (true, vertices_546), (true, vertices_28), (true, vertices_268), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 14 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_355) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_213) then 22 else
  if p.val = (false, vertices_341) then 23 else
  if p.val = (true, vertices_538) then 16 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_538), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 8 538
cert_row_4 1 1 2 3 4 6 188 28 3
cert_row_4 2 2 4 5 6 8 744 168 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 0 0 2 3 4 538 570 3
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 538 794 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 188
cert_cover_5 4 1 1 2 3 4 28 188 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 744
cert_cover_5 7 2 2 4 5 6 168 744 2
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0008

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e11q2_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 91, 227, 409, 617, 425, 278, 710, 838, 338, 812, 436, 676, 856, 736, 19, 67, 131, 25, 41, 73, 393, 145, 97, 161, 22, 582, 134, 262, 82, 274, 194, 322, 148, 276, 164, 292, 548, 644, 772, 88, 280, 296, 552, 584, 776, 336, 400, 224, 608, 416, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_91, vertices_227, vertices_409, vertices_617, vertices_425, vertices_278, vertices_710, vertices_838, vertices_338, vertices_812, vertices_436, vertices_676, vertices_856, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_25, vertices_41, vertices_73, vertices_393, vertices_145, vertices_97, vertices_161, vertices_22, vertices_582, vertices_134, vertices_262, vertices_82, vertices_274, vertices_194, vertices_322, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_280, vertices_296, vertices_552, vertices_584, vertices_776, vertices_336, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_91), (false, vertices_227), (false, vertices_409), (false, vertices_617), (false, vertices_425), (true, vertices_582), (true, vertices_262), (true, vertices_274), (true, vertices_322), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_776), (true, vertices_336), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 15 else
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (true, vertices_582) then 16 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 1 3 4 6 7 436 148 2
cert_row_4 2 1 2 4 7 8 812 292 1
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 582 710 3
cert_coverFacet 2 838
cert_cover_5 2 0 0 1 5 7 582 838 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 292 812 1
cert_coverFacet 5 436
cert_cover_5 5 1 1 3 4 6 148 436 2
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 88 856 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0009

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e11q2_0010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 157, 541, 421, 689, 865, 206, 526, 454, 122, 538, 850, 184, 488, 624, 29, 133, 261, 517, 145, 529, 161, 289, 545, 769, 14, 198, 262, 518, 26, 74, 522, 82, 530, 322, 770, 140, 524, 388, 56, 152, 536, 104, 168, 200, 112, 176, 560, 592, 352, 608, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_157, vertices_541, vertices_421, vertices_689, vertices_865, vertices_206, vertices_526, vertices_454, vertices_122, vertices_538, vertices_850, vertices_184, vertices_488, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_133, vertices_261, vertices_517, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_769, vertices_14, vertices_198, vertices_262, vertices_518, vertices_26, vertices_74, vertices_522, vertices_82, vertices_530, vertices_322, vertices_770, vertices_140, vertices_524, vertices_388, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_200, vertices_112, vertices_176, vertices_560, vertices_592, vertices_352, vertices_608, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_157), (false, vertices_541), (false, vertices_421), (false, vertices_689), (false, vertices_865), (true, vertices_14), (true, vertices_198), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_322), (true, vertices_56), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_112), (true, vertices_592), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_198) then 16 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 454
cert_cover_5 2 0 0 1 5 7 198 454 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 26 122 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 850
cert_cover_5 5 1 0 3 5 7 82 850 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0010

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e11q2_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 173, 57, 665, 369, 417, 961, 158, 302, 662, 838, 90, 362, 932, 120, 25, 41, 137, 49, 81, 529, 161, 289, 321, 577, 385, 641, 14, 150, 262, 518, 26, 298, 74, 82, 530, 322, 578, 44, 140, 164, 292, 644, 772, 56, 88, 152, 104, 112, 656, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_173, vertices_57, vertices_665, vertices_369, vertices_417, vertices_961, vertices_158, vertices_302, vertices_662, vertices_838, vertices_90, vertices_362, vertices_932, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_49, vertices_81, vertices_529, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_150, vertices_262, vertices_518, vertices_26, vertices_298, vertices_74, vertices_82, vertices_530, vertices_322, vertices_578, vertices_44, vertices_140, vertices_164, vertices_292, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_104, vertices_112, vertices_656, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_173), (false, vertices_57), (false, vertices_665), (false, vertices_369), (false, vertices_417), (false, vertices_961), (true, vertices_14), (true, vertices_150), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_298), (true, vertices_74), (true, vertices_322), (true, vertices_292), (true, vertices_644), (true, vertices_772), (true, vertices_88), (true, vertices_104)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 19 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_173) then 14 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_150) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_298) then 18 else
  if p.val = (true, vertices_74) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_104) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_298), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_2 1 0 2 4 7 298
cert_row_4 2 0 1 5 7 8 838 262 2
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 302
cert_cover_5 1 1 0 1 2 4 14 302 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 8 150 662 3
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 262 838 2
cert_coverFacet 4 90
cert_cover_2 4 2 0 3 5 26 90 3
cert_coverFacet 5 362
cert_cover_5 5 1 0 2 4 5 298 362 3
cert_coverFacet 6 932
cert_cover_5 6 3 1 4 6 7 164 932 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0011

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e11q2_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 205, 333, 181, 805, 561, 465, 782, 346, 714, 114, 562, 738, 684, 240, 77, 37, 133, 261, 49, 145, 273, 529, 545, 193, 321, 769, 74, 266, 522, 50, 82, 274, 530, 98, 546, 706, 770, 140, 268, 524, 164, 548, 772, 200, 328, 648, 112, 176, 560, 208, 336, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_205, vertices_333, vertices_181, vertices_805, vertices_561, vertices_465, vertices_782, vertices_346, vertices_714, vertices_114, vertices_562, vertices_738, vertices_684, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_133, vertices_261, vertices_49, vertices_145, vertices_273, vertices_529, vertices_545, vertices_193, vertices_321, vertices_769, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_706, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_772, vertices_200, vertices_328, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_205), (false, vertices_333), (false, vertices_181), (false, vertices_805), (false, vertices_561), (false, vertices_465), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_546), (true, vertices_706), (true, vertices_524), (true, vertices_648), (true, vertices_112), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 16 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_706) then 15 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 7 346 74 2
cert_row_2 1 0 5 6 8 706
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 74 346 2
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 74 714 3
cert_coverFacet 3 114
cert_cover_2 3 3 0 4 5 50 114 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 98 738 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0012

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e11q2_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 301, 565, 661, 453, 865, 62, 90, 554, 842, 690, 210, 412, 472, 808, 533, 37, 133, 261, 289, 545, 193, 321, 577, 641, 26, 42, 74, 522, 50, 82, 146, 546, 194, 578, 642, 28, 44, 268, 52, 148, 388, 88, 408, 296, 552, 328, 776, 560, 208, 656, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_301, vertices_565, vertices_661, vertices_453, vertices_865, vertices_62, vertices_90, vertices_554, vertices_842, vertices_690, vertices_210, vertices_412, vertices_472, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_37, vertices_133, vertices_261, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_82, vertices_146, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_268, vertices_52, vertices_148, vertices_388, vertices_88, vertices_408, vertices_296, vertices_552, vertices_328, vertices_776, vertices_560, vertices_208, vertices_656, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_301), (false, vertices_565), (false, vertices_661), (false, vertices_453), (false, vertices_865), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_546), (true, vertices_28), (true, vertices_88), (true, vertices_408), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_408) then 18 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 4 62 26 1
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_2 2 2 3 6 7 408
cert_row_4 3 0 3 4 6 8 690 50 3
cert_rows
cert_pivot_2 1 5 2 0
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 26 62 1
cert_coverFacet 1 90
cert_cover_2 1 2 0 3 5 26 90 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 74 842 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 50 690 3
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 412
cert_cover_5 6 2 1 2 3 6 28 412 3
cert_coverFacet 7 472
cert_cover_5 7 2 2 3 5 6 88 472 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0013

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e11q2_0015.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 653, 805, 569, 361, 457, 598, 278, 710, 122, 306, 482, 788, 728, 816, 133, 261, 517, 41, 329, 137, 521, 289, 545, 385, 22, 582, 134, 262, 50, 82, 274, 98, 290, 194, 386, 276, 532, 644, 772, 56, 88, 536, 104, 200, 648, 304, 560, 592, 784, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_653, vertices_805, vertices_569, vertices_361, vertices_457, vertices_598, vertices_278, vertices_710, vertices_122, vertices_306, vertices_482, vertices_788, vertices_728, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_329, vertices_137, vertices_521, vertices_289, vertices_545, vertices_385, vertices_22, vertices_582, vertices_134, vertices_262, vertices_50, vertices_82, vertices_274, vertices_98, vertices_290, vertices_194, vertices_386, vertices_276, vertices_532, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_200, vertices_648, vertices_304, vertices_560, vertices_592, vertices_784, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_653), (false, vertices_805), (false, vertices_569), (false, vertices_361), (false, vertices_457), (true, vertices_22), (true, vertices_582), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_194), (true, vertices_276), (true, vertices_532), (true, vertices_88), (true, vertices_304), (true, vertices_592), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_582) then 16 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_4 2 0 2 3 4 5 122 50 1
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 710
cert_cover_5 2 0 0 1 5 6 582 710 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 50 122 1
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 98 482 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0015

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e11q2_0016.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 405, 661, 613, 481, 286, 58, 234, 458, 562, 914, 540, 588, 632, 149, 69, 261, 517, 97, 161, 545, 321, 385, 641, 26, 42, 202, 266, 50, 274, 530, 162, 546, 386, 642, 28, 76, 268, 524, 276, 532, 580, 56, 536, 104, 328, 584, 560, 400, 656, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_405, vertices_661, vertices_613, vertices_481, vertices_286, vertices_58, vertices_234, vertices_458, vertices_562, vertices_914, vertices_540, vertices_588, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_26, vertices_42, vertices_202, vertices_266, vertices_50, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_580, vertices_56, vertices_536, vertices_104, vertices_328, vertices_584, vertices_560, vertices_400, vertices_656, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_405), (false, vertices_661), (false, vertices_613), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_202), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_28), (true, vertices_524), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_584), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 17 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_560) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 7 286 26 1
cert_row_4 1 0 3 6 7 8 914 274 2
cert_row_2 2 0 2 5 6 202
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 26 286 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 234
cert_cover_5 2 2 0 2 4 5 42 234 3
cert_coverFacet 3 458
cert_cover_5 3 2 0 2 5 7 202 458 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 914
cert_cover_5 5 1 0 3 6 7 274 914 2
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 56 632 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0016

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e11q2_0017.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 659, 227, 355, 333, 713, 182, 562, 802, 604, 284, 308, 724, 484, 824, 99, 131, 259, 515, 73, 265, 521, 193, 321, 641, 50, 146, 530, 162, 290, 546, 770, 28, 76, 268, 52, 596, 148, 276, 164, 292, 196, 324, 280, 536, 584, 776, 304, 560, 656, 224, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_659, vertices_227, vertices_355, vertices_333, vertices_713, vertices_182, vertices_562, vertices_802, vertices_604, vertices_284, vertices_308, vertices_724, vertices_484, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_99, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_268, vertices_52, vertices_596, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_280, vertices_536, vertices_584, vertices_776, vertices_304, vertices_560, vertices_656, vertices_224, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_659), (false, vertices_227), (false, vertices_355), (false, vertices_333), (false, vertices_713), (true, vertices_50), (true, vertices_546), (true, vertices_28), (true, vertices_52), (true, vertices_596), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_280), (true, vertices_536), (true, vertices_304), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 14 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_659) then 21 else
  if p.val = (false, vertices_227) then 22 else
  if p.val = (false, vertices_355) then 23 else
  if p.val = (false, vertices_333) then 15 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_596) then 16 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 50 1
cert_row_4 1 1 4 5 6 7 484 164 2
cert_row_2 2 1 3 5 8 596
cert_row_4 3 2 3 4 7 8 824 280 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 50 182 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 28 604 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 724
cert_cover_5 6 2 1 3 5 6 596 724 3
cert_coverFacet 7 484
cert_cover_5 7 1 1 4 5 6 164 484 2
cert_coverFacet 8 824
cert_cover_5 8 3 2 3 4 7 280 824 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0017

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e11q2_0018.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 61, 793, 361, 689, 737, 158, 302, 358, 710, 394, 898, 244, 408, 912, 25, 41, 265, 49, 529, 97, 673, 321, 577, 769, 14, 294, 70, 134, 138, 266, 322, 578, 386, 642, 770, 28, 44, 52, 148, 100, 196, 152, 280, 296, 392, 176, 400, 656, 784, 224, 352, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_61, vertices_793, vertices_361, vertices_689, vertices_737, vertices_158, vertices_302, vertices_358, vertices_710, vertices_394, vertices_898, vertices_244, vertices_408, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_49, vertices_529, vertices_97, vertices_673, vertices_321, vertices_577, vertices_769, vertices_14, vertices_294, vertices_70, vertices_134, vertices_138, vertices_266, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_52, vertices_148, vertices_100, vertices_196, vertices_152, vertices_280, vertices_296, vertices_392, vertices_176, vertices_400, vertices_656, vertices_784, vertices_224, vertices_352, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_61), (false, vertices_793), (false, vertices_361), (false, vertices_689), (false, vertices_737), (true, vertices_14), (true, vertices_294), (true, vertices_70), (true, vertices_134), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_100), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_400), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_294) then 16 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_2 0 0 1 4 7 294
cert_row_4 1 0 1 2 3 6 158 14 3
cert_row_4 2 0 1 5 6 8 710 70 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 14 158 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 4 14 302 3
cert_coverFacet 2 358
cert_cover_5 2 0 0 1 4 5 294 358 3
cert_coverFacet 3 710
cert_cover_5 3 2 0 1 5 6 70 710 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 912
cert_cover_2 8 6 3 7 8 400 912 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0018

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e11q2_0019.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 563, 355, 451, 117, 721, 398, 778, 802, 604, 284, 716, 308, 484, 824, 35, 323, 131, 515, 49, 81, 529, 97, 193, 641, 138, 266, 522, 290, 546, 386, 770, 28, 588, 140, 268, 52, 84, 276, 100, 292, 196, 388, 280, 536, 648, 776, 304, 560, 592, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_563, vertices_355, vertices_451, vertices_117, vertices_721, vertices_398, vertices_778, vertices_802, vertices_604, vertices_284, vertices_716, vertices_308, vertices_484, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_323, vertices_131, vertices_515, vertices_49, vertices_81, vertices_529, vertices_97, vertices_193, vertices_641, vertices_138, vertices_266, vertices_522, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_588, vertices_140, vertices_268, vertices_52, vertices_84, vertices_276, vertices_100, vertices_292, vertices_196, vertices_388, vertices_280, vertices_536, vertices_648, vertices_776, vertices_304, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_563), (false, vertices_355), (false, vertices_451), (false, vertices_117), (false, vertices_721), (true, vertices_266), (true, vertices_770), (true, vertices_28), (true, vertices_588), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_304), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 14 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_563) then 20 else
  if p.val = (false, vertices_355) then 21 else
  if p.val = (false, vertices_451) then 22 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_588) then 16 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 7 398 138 1
cert_row_4 1 1 4 5 6 7 484 100 3
cert_row_2 2 1 2 5 8 588
cert_row_4 3 2 3 4 7 8 824 280 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 28 604 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 716
cert_cover_5 5 2 1 2 5 6 588 716 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 484
cert_cover_5 7 1 1 4 5 6 100 484 3
cert_coverFacet 8 824
cert_cover_5 8 3 2 3 4 7 280 824 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0019

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e11q2_0021.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0021

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 589, 341, 421, 677, 625, 654, 58, 218, 554, 466, 930, 460, 568, 600, 165, 69, 261, 517, 49, 81, 273, 289, 545, 577, 26, 42, 138, 522, 50, 210, 274, 290, 546, 386, 642, 76, 140, 524, 324, 388, 644, 56, 88, 536, 552, 200, 584, 560, 336, 592, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_589, vertices_341, vertices_421, vertices_677, vertices_625, vertices_654, vertices_58, vertices_218, vertices_554, vertices_466, vertices_930, vertices_460, vertices_568, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_165, vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_210, vertices_274, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_524, vertices_324, vertices_388, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_584, vertices_560, vertices_336, vertices_592, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_589), (false, vertices_341), (false, vertices_421), (false, vertices_677), (false, vertices_625), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_210), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_677) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_210) then 16 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 6 210
cert_row_4 1 0 4 6 7 8 930 290 2
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 218
cert_cover_5 2 0 0 2 3 5 26 218 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 7 210 466 3
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 290 930 2
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0021

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e11q2_0022.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 589, 341, 901, 233, 481, 406, 662, 58, 538, 426, 370, 628, 568, 616, 69, 261, 517, 73, 137, 521, 225, 321, 385, 641, 150, 26, 42, 138, 522, 50, 274, 530, 290, 386, 642, 84, 276, 532, 580, 388, 644, 56, 536, 104, 168, 552, 584, 112, 560, 336, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_589, vertices_341, vertices_901, vertices_233, vertices_481, vertices_406, vertices_662, vertices_58, vertices_538, vertices_426, vertices_370, vertices_628, vertices_568, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_225, vertices_321, vertices_385, vertices_641, vertices_150, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_386, vertices_642, vertices_84, vertices_276, vertices_532, vertices_580, vertices_388, vertices_644, vertices_56, vertices_536, vertices_104, vertices_168, vertices_552, vertices_584, vertices_112, vertices_560, vertices_336, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_589), (false, vertices_341), (false, vertices_901), (false, vertices_233), (false, vertices_481), (true, vertices_150), (true, vertices_26), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_386), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_150) then 16 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 0 1 3 6 150
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 7 150 406 3
cert_coverFacet 1 662
cert_cover_5 1 1 0 1 3 8 150 662 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 426
cert_cover_5 4 0 0 2 4 6 42 426 3
cert_coverFacet 5 370
cert_cover_5 5 2 0 3 4 5 50 370 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 84 628 2
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0022

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e11q2_0023.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 397, 309, 565, 709, 809, 598, 58, 538, 234, 370, 706, 468, 568, 488, 53, 133, 261, 517, 137, 265, 521, 289, 545, 641, 26, 42, 138, 522, 50, 82, 530, 98, 194, 578, 642, 84, 276, 532, 196, 580, 388, 56, 536, 232, 296, 552, 392, 304, 560, 336, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_397, vertices_309, vertices_565, vertices_709, vertices_809, vertices_598, vertices_58, vertices_538, vertices_234, vertices_370, vertices_706, vertices_468, vertices_568, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_53, vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_289, vertices_545, vertices_641, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_194, vertices_578, vertices_642, vertices_84, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_56, vertices_536, vertices_232, vertices_296, vertices_552, vertices_392, vertices_304, vertices_560, vertices_336, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_397), (false, vertices_309), (false, vertices_565), (false, vertices_709), (false, vertices_809), (true, vertices_26), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_194), (true, vertices_578), (true, vertices_84), (true, vertices_56), (true, vertices_536), (true, vertices_232), (true, vertices_336), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 20 16 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_565) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_232) then 19 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 5 6 232
cert_row_4 1 0 1 3 5 8 598 82 1
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 82 598 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 234
cert_cover_5 3 0 0 2 4 5 42 234 3
cert_coverFacet 4 370
cert_cover_5 4 2 0 3 4 5 50 370 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 84 468 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 488
cert_cover_5 8 0 2 4 5 7 232 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0023

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e11q2_0024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 803, 781, 677, 453, 241, 542, 58, 106, 842, 690, 412, 660, 120, 472, 291, 133, 261, 517, 97, 161, 545, 193, 321, 769, 26, 42, 74, 522, 50, 530, 98, 546, 322, 770, 28, 268, 524, 148, 532, 388, 644, 56, 88, 408, 104, 328, 776, 112, 176, 208, 656, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_803, vertices_781, vertices_677, vertices_453, vertices_241, vertices_542, vertices_58, vertices_106, vertices_842, vertices_690, vertices_412, vertices_660, vertices_120, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_291, vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_769, vertices_26, vertices_42, vertices_74, vertices_522, vertices_50, vertices_530, vertices_98, vertices_546, vertices_322, vertices_770, vertices_28, vertices_268, vertices_524, vertices_148, vertices_532, vertices_388, vertices_644, vertices_56, vertices_88, vertices_408, vertices_104, vertices_328, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_803), (false, vertices_781), (false, vertices_677), (false, vertices_453), (false, vertices_241), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_28), (true, vertices_148), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_408), (true, vertices_104), (true, vertices_328), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 15 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_408) then 22 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_2 2 2 3 6 7 408
cert_row_4 3 0 3 4 6 8 690 50 3
cert_rows
cert_pivot_2 1 5 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 106
cert_cover_2 2 2 0 4 5 42 106 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 74 842 3
cert_coverFacet 4 690
cert_cover_5 4 3 0 3 4 6 50 690 3
cert_coverFacet 5 412
cert_cover_5 5 2 1 2 3 6 28 412 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 472
cert_cover_5 8 2 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0024

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e11q2_0025.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0025

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 781, 661, 421, 713, 481, 566, 218, 666, 810, 306, 338, 244, 804, 368, 133, 261, 517, 73, 265, 521, 417, 193, 321, 641, 154, 74, 266, 522, 50, 82, 274, 530, 290, 546, 322, 52, 148, 532, 164, 292, 548, 772, 200, 648, 776, 112, 304, 208, 336, 656, 224, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_781, vertices_661, vertices_421, vertices_713, vertices_481, vertices_566, vertices_218, vertices_666, vertices_810, vertices_306, vertices_338, vertices_244, vertices_804, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_417, vertices_193, vertices_321, vertices_641, vertices_154, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_322, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_772, vertices_200, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_781), (false, vertices_661), (false, vertices_421), (false, vertices_713), (false, vertices_481), (true, vertices_154), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_52), (true, vertices_548), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_421) then 24 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_154) then 16 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_2 1 0 2 3 6 154
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 154 218 3
cert_coverFacet 2 666
cert_cover_5 2 1 0 2 3 8 154 666 3
cert_coverFacet 3 810
cert_cover_5 3 0 0 2 4 7 266 810 2
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0025

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e11q2_0026.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0026

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 307, 563, 707, 665, 465, 590, 774, 802, 572, 236, 484, 804, 440, 712, 51, 67, 259, 515, 145, 273, 529, 193, 321, 641, 70, 262, 518, 290, 546, 578, 770, 44, 76, 524, 228, 292, 548, 324, 772, 56, 152, 536, 168, 200, 584, 648, 304, 560, 400, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_307, vertices_563, vertices_707, vertices_665, vertices_465, vertices_590, vertices_774, vertices_802, vertices_572, vertices_236, vertices_484, vertices_804, vertices_440, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_67, vertices_259, vertices_515, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_70, vertices_262, vertices_518, vertices_290, vertices_546, vertices_578, vertices_770, vertices_44, vertices_76, vertices_524, vertices_228, vertices_292, vertices_548, vertices_324, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_400, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_307), (false, vertices_563), (false, vertices_707), (false, vertices_665), (false, vertices_465), (true, vertices_518), (true, vertices_770), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_228), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_56), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_563) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_228) then 16 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 1 4 5 6 228
cert_row_4 2 1 2 3 4 8 572 44 2
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 572
cert_cover_5 3 2 1 2 3 4 44 572 2
cert_coverFacet 4 236
cert_cover_5 4 1 1 2 4 5 44 236 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 7 228 484 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 56 440 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0026

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e11q2_0027.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0027

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 587, 397, 661, 837, 681, 598, 570, 426, 306, 338, 244, 484, 368, 688, 75, 133, 261, 517, 137, 265, 521, 321, 577, 641, 42, 266, 522, 50, 82, 274, 530, 290, 322, 578, 84, 148, 532, 228, 324, 580, 388, 168, 552, 392, 112, 176, 304, 560, 336, 656, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_587, vertices_397, vertices_661, vertices_837, vertices_681, vertices_598, vertices_570, vertices_426, vertices_306, vertices_338, vertices_244, vertices_484, vertices_368, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_133, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_42, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_322, vertices_578, vertices_84, vertices_148, vertices_532, vertices_228, vertices_324, vertices_580, vertices_388, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_656, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_587), (false, vertices_397), (false, vertices_661), (false, vertices_837), (false, vertices_681), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_84), (true, vertices_228), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_228) then 23 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 1 4 5 6 228
cert_row_4 2 0 1 3 5 8 598 82 1
cert_row_4 3 0 2 3 4 8 570 42 2
cert_rows
cert_pivot_2 7 6 1 0
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 82 598 1
cert_coverFacet 1 570
cert_cover_5 1 3 0 2 3 4 42 570 2
cert_coverFacet 2 426
cert_cover_5 2 0 0 2 4 6 42 426 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 244
cert_cover_5 5 1 1 3 4 5 84 244 2
cert_coverFacet 6 484
cert_cover_5 6 1 1 4 5 7 228 484 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0027

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e11q2_0028.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 659, 803, 195, 569, 433, 449, 206, 646, 774, 668, 620, 868, 376, 472, 67, 131, 259, 515, 49, 145, 529, 289, 545, 193, 321, 385, 70, 134, 262, 518, 194, 642, 770, 76, 140, 524, 612, 324, 644, 772, 56, 344, 152, 536, 104, 552, 200, 304, 400, 656, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_659, vertices_803, vertices_195, vertices_569, vertices_433, vertices_449, vertices_206, vertices_646, vertices_774, vertices_668, vertices_620, vertices_868, vertices_376, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_70, vertices_134, vertices_262, vertices_518, vertices_194, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_612, vertices_324, vertices_644, vertices_772, vertices_56, vertices_344, vertices_152, vertices_536, vertices_104, vertices_552, vertices_200, vertices_304, vertices_400, vertices_656, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_659), (false, vertices_803), (false, vertices_195), (false, vertices_569), (false, vertices_433), (false, vertices_449), (true, vertices_134), (true, vertices_518), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_612), (true, vertices_644), (true, vertices_772), (true, vertices_344), (true, vertices_152), (true, vertices_104), (true, vertices_200), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_344) then 21 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_2 1 2 3 5 7 344
cert_row_4 2 0 1 2 5 6 206 70 2
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 70 206 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 668
cert_cover_5 3 3 1 2 3 6 140 668 2
cert_coverFacet 4 620
cert_cover_5 4 0 1 2 4 5 76 620 2
cert_coverFacet 5 868
cert_cover_5 5 0 1 4 5 7 612 868 3
cert_coverFacet 6 376
cert_cover_5 6 1 2 3 4 5 56 376 3
cert_coverFacet 7 472
cert_cover_5 7 1 2 3 5 6 344 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0028

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e11q2_0029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 557, 229, 901, 409, 537, 169, 118, 566, 710, 346, 962, 120, 568, 488, 37, 133, 517, 25, 41, 137, 521, 273, 529, 161, 385, 769, 54, 70, 518, 82, 274, 530, 706, 322, 770, 100, 548, 196, 644, 56, 88, 280, 536, 104, 168, 552, 328, 392, 112, 560, 224, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_557, vertices_229, vertices_901, vertices_409, vertices_537, vertices_169, vertices_118, vertices_566, vertices_710, vertices_346, vertices_962, vertices_120, vertices_568, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_25, vertices_41, vertices_137, vertices_521, vertices_273, vertices_529, vertices_161, vertices_385, vertices_769, vertices_54, vertices_70, vertices_518, vertices_82, vertices_274, vertices_530, vertices_706, vertices_322, vertices_770, vertices_100, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_168, vertices_552, vertices_328, vertices_392, vertices_112, vertices_560, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_557), (false, vertices_229), (false, vertices_901), (false, vertices_409), (false, vertices_537), (false, vertices_169), (true, vertices_54), (true, vertices_70), (true, vertices_518), (true, vertices_82), (true, vertices_706), (true, vertices_322), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_560), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 16 13 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 21 else
  if p.val = (false, vertices_557) then 14 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_409) then 15 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (true, vertices_54) then 19 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_706) then 22 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 8 706
cert_row_2 1 0 1 3 4 54
cert_row_4 2 0 2 3 5 7 346 82 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 5 54 118 3
cert_coverFacet 1 566
cert_cover_5 1 1 0 1 3 8 54 566 3
cert_coverFacet 2 710
cert_cover_5 2 0 0 1 5 6 70 710 3
cert_coverFacet 3 346
cert_cover_5 3 2 0 2 3 5 82 346 1
cert_coverFacet 4 962
cert_cover_5 4 0 0 5 6 7 706 962 3
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0029

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e11q2_0030.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0030

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 653, 277, 533, 453, 233, 841, 310, 122, 602, 482, 834, 692, 420, 696, 21, 133, 261, 517, 73, 137, 521, 273, 529, 193, 321, 769, 90, 50, 274, 530, 98, 290, 322, 578, 770, 52, 276, 532, 164, 292, 388, 644, 56, 536, 104, 168, 584, 648, 688, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_653, vertices_277, vertices_533, vertices_453, vertices_233, vertices_841, vertices_310, vertices_122, vertices_602, vertices_482, vertices_834, vertices_692, vertices_420, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_273, vertices_529, vertices_193, vertices_321, vertices_769, vertices_90, vertices_50, vertices_274, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_388, vertices_644, vertices_56, vertices_536, vertices_104, vertices_168, vertices_584, vertices_648, vertices_688, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_653), (false, vertices_277), (false, vertices_533), (false, vertices_453), (false, vertices_233), (false, vertices_841), (true, vertices_90), (true, vertices_50), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_52), (true, vertices_164), (true, vertices_292), (true, vertices_56), (true, vertices_536), (true, vertices_688), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_688) then 23 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_2 1 3 4 6 8 688
cert_row_4 2 0 1 3 4 7 310 50 1
cert_row_4 3 0 4 5 6 7 482 98 3
cert_rows
cert_pivot_2 2 8 1 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 2 0 1 3 4 50 310 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 90 122 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 98 482 3
cert_coverFacet 4 834
cert_cover_2 4 5 0 7 8 322 834 3
cert_coverFacet 5 692
cert_cover_5 5 1 1 3 4 6 52 692 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 696
cert_cover_5 7 1 2 3 4 6 56 696 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0030

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e11q2_0031.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0031

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 589, 805, 453, 57, 537, 361, 214, 598, 902, 186, 930, 472, 600, 424, 69, 261, 517, 25, 41, 73, 521, 49, 529, 289, 545, 321, 86, 134, 518, 50, 146, 530, 162, 546, 898, 196, 580, 388, 772, 56, 88, 152, 536, 168, 296, 328, 584, 392, 208, 592, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_589, vertices_805, vertices_453, vertices_57, vertices_537, vertices_361, vertices_214, vertices_598, vertices_902, vertices_186, vertices_930, vertices_472, vertices_600, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_25, vertices_41, vertices_73, vertices_521, vertices_49, vertices_529, vertices_289, vertices_545, vertices_321, vertices_86, vertices_134, vertices_518, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_898, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_296, vertices_328, vertices_584, vertices_392, vertices_208, vertices_592, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_589), (false, vertices_805), (false, vertices_453), (false, vertices_57), (false, vertices_537), (false, vertices_361), (true, vertices_86), (true, vertices_134), (true, vertices_518), (true, vertices_146), (true, vertices_162), (true, vertices_898), (true, vertices_88), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_592), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 16 13 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 21 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_361) then 15 else
  if p.val = (true, vertices_86) then 19 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_898) then 22 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 6 7 8 898
cert_row_2 1 0 1 3 5 86
cert_row_4 2 0 2 3 4 6 186 50 1
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 8 86 598 3
cert_coverFacet 2 902
cert_cover_5 2 0 0 1 6 7 134 902 3
cert_coverFacet 3 186
cert_cover_5 3 2 0 2 3 4 50 186 1
cert_coverFacet 4 930
cert_cover_5 4 0 0 4 6 7 162 930 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 88 472 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0031

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e11q2_0032.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0032

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 551, 395, 707, 781, 601, 201, 434, 674, 372, 852, 740, 248, 408, 792, 39, 131, 259, 515, 261, 517, 73, 137, 265, 521, 193, 577, 162, 290, 546, 386, 642, 340, 100, 292, 548, 580, 772, 88, 152, 280, 536, 200, 392, 776, 112, 176, 304, 592, 400, 784, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_551, vertices_395, vertices_707, vertices_781, vertices_601, vertices_201, vertices_434, vertices_674, vertices_372, vertices_852, vertices_740, vertices_248, vertices_408, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_131, vertices_259, vertices_515, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_193, vertices_577, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_340, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_784, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_551), (false, vertices_395), (false, vertices_707), (false, vertices_781), (false, vertices_601), (false, vertices_201), (true, vertices_162), (true, vertices_340), (true, vertices_100), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_400), (true, vertices_784), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 13 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 18 else
  if p.val = (false, vertices_551) then 19 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_781) then 15 else
  if p.val = (false, vertices_601) then 16 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_340) then 22 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 162 1
cert_row_2 1 1 3 5 7 340
cert_row_4 2 1 4 5 6 8 740 100 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 434
cert_cover_5 0 0 0 3 4 6 162 434 1
cert_coverFacet 1 674
cert_cover_2 1 4 0 6 8 162 674 3
cert_coverFacet 2 372
cert_cover_5 2 1 1 3 4 5 340 372 2
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 8 340 852 3
cert_coverFacet 4 740
cert_cover_5 4 2 1 4 5 6 100 740 3
cert_coverFacet 5 248
cert_cover_5 5 3 2 3 4 5 88 248 2
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0032

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e11q2_0033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 809, 713, 241, 433, 302, 558, 342, 534, 722, 354, 668, 404, 368, 137, 265, 521, 177, 97, 289, 545, 193, 577, 385, 46, 22, 262, 518, 82, 530, 98, 290, 546, 322, 578, 140, 268, 524, 148, 276, 532, 388, 296, 552, 648, 112, 304, 208, 336, 400, 656, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_809, vertices_713, vertices_241, vertices_433, vertices_302, vertices_558, vertices_342, vertices_534, vertices_722, vertices_354, vertices_668, vertices_404, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_177, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_46, vertices_22, vertices_262, vertices_518, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_296, vertices_552, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_809), (false, vertices_713), (false, vertices_241), (false, vertices_433), (true, vertices_46), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_530), (true, vertices_290), (true, vertices_322), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_336), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 1 3 5 7 342 22 3
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 1 2 3 6 8 668 140 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 342
cert_cover_5 2 1 0 1 3 5 22 342 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 82 722 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 668
cert_cover_5 6 3 1 2 3 6 140 668 2
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0033

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e11q2_0034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 781, 213, 341, 677, 713, 566, 794, 234, 682, 306, 354, 180, 788, 496, 85, 133, 261, 517, 73, 265, 521, 193, 321, 641, 170, 74, 266, 522, 50, 274, 530, 98, 290, 546, 322, 52, 148, 276, 532, 164, 548, 772, 200, 648, 776, 176, 304, 208, 336, 784, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_781, vertices_213, vertices_341, vertices_677, vertices_713, vertices_566, vertices_794, vertices_234, vertices_682, vertices_306, vertices_354, vertices_180, vertices_788, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_85, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_170, vertices_74, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_772, vertices_200, vertices_648, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_781), (false, vertices_213), (false, vertices_341), (false, vertices_677), (false, vertices_713), (true, vertices_170), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_52), (true, vertices_532), (true, vertices_176), (true, vertices_304), (true, vertices_784), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_213) then 21 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_677) then 23 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (true, vertices_170) then 16 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 50 1
cert_row_4 1 0 2 3 7 8 794 266 2
cert_row_2 2 0 2 4 6 170
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 50 566 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 266 794 2
cert_coverFacet 2 234
cert_cover_5 2 2 0 2 4 5 170 234 3
cert_coverFacet 3 682
cert_cover_5 3 2 0 2 4 8 170 682 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0034

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e11q2_0035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 205, 421, 345, 905, 182, 214, 806, 794, 562, 338, 632, 744, 240, 928, 69, 133, 261, 73, 137, 265, 321, 385, 150, 38, 70, 262, 50, 82, 274, 530, 546, 322, 770, 164, 292, 196, 88, 280, 536, 616, 200, 648, 776, 112, 176, 560, 208, 336, 224, 416, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_205, vertices_421, vertices_345, vertices_905, vertices_182, vertices_214, vertices_806, vertices_794, vertices_562, vertices_338, vertices_632, vertices_744, vertices_240, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_73, vertices_137, vertices_265, vertices_321, vertices_385, vertices_150, vertices_38, vertices_70, vertices_262, vertices_50, vertices_82, vertices_274, vertices_530, vertices_546, vertices_322, vertices_770, vertices_164, vertices_292, vertices_196, vertices_88, vertices_280, vertices_536, vertices_616, vertices_200, vertices_648, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_336, vertices_224, vertices_416, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_205), (false, vertices_421), (false, vertices_345), (false, vertices_905), (true, vertices_150), (true, vertices_38), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_536), (true, vertices_616), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_224), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (true, vertices_150) then 17 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_616) then 24 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 24 => Sum.inr ⟨(true, vertices_616), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 5 8 616
cert_row_2 1 0 1 3 6 150
cert_row_4 2 0 1 4 7 8 806 38 3
cert_row_4 3 0 2 3 7 8 794 274 1
cert_rows
cert_pivot_2 5 6 1 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 150 182 3
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 5 150 214 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 7 38 806 3
cert_coverFacet 3 794
cert_cover_5 3 3 0 2 3 7 274 794 1
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 632
cert_cover_5 6 0 2 3 4 5 88 632 2
cert_coverFacet 7 744
cert_cover_5 7 0 2 4 5 6 616 744 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coverFacet 9 928
cert_cover_2 9 6 4 7 8 416 928 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0035

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e11q2_0036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 453, 569, 425, 713, 353, 214, 278, 358, 314, 562, 722, 796, 908, 660, 41, 137, 521, 97, 289, 545, 193, 321, 577, 385, 22, 70, 262, 50, 210, 274, 530, 98, 290, 546, 578, 780, 148, 276, 532, 196, 324, 388, 644, 56, 280, 536, 296, 392, 648, 560, 656, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_453, vertices_569, vertices_425, vertices_713, vertices_353, vertices_214, vertices_278, vertices_358, vertices_314, vertices_562, vertices_722, vertices_796, vertices_908, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_22, vertices_70, vertices_262, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_578, vertices_780, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_280, vertices_536, vertices_296, vertices_392, vertices_648, vertices_560, vertices_656, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_453), (false, vertices_569), (false, vertices_425), (false, vertices_713), (false, vertices_353), (true, vertices_22), (true, vertices_70), (true, vertices_262), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_780), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_280), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_210) then 16 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_780) then 19 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 4 5 7 358 70 2
cert_row_4 3 0 2 3 4 7 314 50 1
cert_rows
cert_pivot_2 8 6 1 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 358
cert_cover_5 2 2 0 1 4 5 70 358 2
cert_coverFacet 3 314
cert_cover_5 3 3 0 2 3 4 50 314 1
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 8 210 722 3
cert_coverFacet 6 796
cert_cover_5 6 0 1 2 3 7 780 796 2
cert_coverFacet 7 908
cert_cover_5 7 0 1 2 6 7 780 908 2
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0036

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e11q2_0038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 357, 677, 581, 185, 305, 465, 838, 218, 346, 682, 778, 572, 796, 308, 37, 69, 517, 49, 145, 273, 161, 289, 193, 321, 577, 641, 90, 138, 266, 522, 194, 322, 578, 642, 770, 540, 52, 276, 292, 548, 324, 580, 772, 56, 152, 280, 168, 552, 776, 304, 208, 336, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_357, vertices_677, vertices_581, vertices_185, vertices_305, vertices_465, vertices_838, vertices_218, vertices_346, vertices_682, vertices_778, vertices_572, vertices_796, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_49, vertices_145, vertices_273, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_90, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_540, vertices_52, vertices_276, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_552, vertices_776, vertices_304, vertices_208, vertices_336, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_357), (false, vertices_677), (false, vertices_581), (false, vertices_185), (false, vertices_305), (false, vertices_465), (true, vertices_90), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_322), (true, vertices_770), (true, vertices_540), (true, vertices_52), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_552), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_90) then 15 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_540) then 19 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_776) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_540), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
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
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_2 1 0 2 3 5 90
cert_row_2 2 1 2 3 8 540
cert_row_4 3 0 2 4 6 8 682 138 2
cert_rows
cert_pivot_2 7 5 1 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 6 90 218 3
cert_coverFacet 2 346
cert_cover_5 2 1 0 2 3 7 90 346 3
cert_coverFacet 3 682
cert_cover_5 3 3 0 2 4 6 138 682 2
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 572
cert_cover_5 5 2 1 2 3 4 540 572 3
cert_coverFacet 6 796
cert_cover_5 6 2 1 2 3 7 540 796 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0038

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e11q2_0039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 29, 205, 309, 613, 57, 681, 214, 342, 410, 906, 866, 156, 356, 824, 13, 21, 37, 69, 25, 41, 137, 49, 545, 193, 577, 641, 86, 394, 146, 274, 194, 322, 578, 642, 770, 28, 140, 148, 276, 100, 292, 196, 324, 56, 152, 280, 552, 648, 776, 304, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_29, vertices_205, vertices_309, vertices_613, vertices_57, vertices_681, vertices_214, vertices_342, vertices_410, vertices_906, vertices_866, vertices_156, vertices_356, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_69, vertices_25, vertices_41, vertices_137, vertices_49, vertices_545, vertices_193, vertices_577, vertices_641, vertices_86, vertices_394, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_140, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_56, vertices_152, vertices_280, vertices_552, vertices_648, vertices_776, vertices_304, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_29), (false, vertices_205), (false, vertices_309), (false, vertices_613), (false, vertices_57), (false, vertices_681), (true, vertices_86), (true, vertices_394), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_770), (true, vertices_148), (true, vertices_324), (true, vertices_152), (true, vertices_280), (true, vertices_776), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 13 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_205) then 20 else
  if p.val = (false, vertices_309) then 14 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (true, vertices_86) then 15 else
  if p.val = (true, vertices_394) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 394 410 2
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 8 394 906 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0039

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e11q2_0040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 29, 397, 789, 681, 961, 94, 110, 554, 722, 482, 674, 428, 372, 848, 13, 21, 261, 25, 137, 521, 529, 385, 641, 769, 78, 26, 42, 522, 82, 530, 98, 162, 546, 194, 642, 28, 44, 396, 84, 276, 100, 292, 168, 552, 336, 592, 784, 352, 416, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_29, vertices_397, vertices_789, vertices_681, vertices_961, vertices_94, vertices_110, vertices_554, vertices_722, vertices_482, vertices_674, vertices_428, vertices_372, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_25, vertices_137, vertices_521, vertices_529, vertices_385, vertices_641, vertices_769, vertices_78, vertices_26, vertices_42, vertices_522, vertices_82, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_28, vertices_44, vertices_396, vertices_84, vertices_276, vertices_100, vertices_292, vertices_168, vertices_552, vertices_336, vertices_592, vertices_784, vertices_352, vertices_416, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_29), (false, vertices_397), (false, vertices_789), (false, vertices_681), (false, vertices_961), (true, vertices_78), (true, vertices_42), (true, vertices_82), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_642), (true, vertices_44), (true, vertices_84), (true, vertices_100), (true, vertices_292), (true, vertices_336), (true, vertices_592), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 26 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 17 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_961) then 27 else
  if p.val = (true, vertices_78) then 18 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_352) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 82 3
cert_row_4 1 1 3 4 5 7 372 84 2
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_2 3 0 1 2 5 78
cert_row_2 4 1 2 6 7 396
cert_rows_2
cert_pivot 8 3 4 0 1
cert_heightProof 5
cert_coverFacet 0 94
cert_cover_5 0 3 0 1 2 3 78 94 3
cert_coverFacet 1 110
cert_cover_5 1 3 0 1 2 4 78 110 3
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 722
cert_cover_5 3 0 0 3 5 6 82 722 3
cert_coverFacet 4 482
cert_cover_5 4 2 0 4 5 6 98 482 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 428
cert_cover_5 6 4 1 2 4 6 44 428 3
cert_coverFacet 7 372
cert_cover_5 7 1 1 3 4 5 84 372 2
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 5 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0040

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3813 : Certifies 3813 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0008.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3814 : Certifies 3814 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3815 : Certifies 3815 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3816 : Certifies 3816 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3817 : Certifies 3817 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3818 : Certifies 3818 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3819 : Certifies 3819 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0015.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3820 : Certifies 3820 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0016.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3821 : Certifies 3821 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0017.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3822 : Certifies 3822 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0018.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3823 : Certifies 3823 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0019.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3824 : Certifies 3824 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0021.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3825 : Certifies 3825 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0022.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3826 : Certifies 3826 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0023.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3827 : Certifies 3827 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3828 : Certifies 3828 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0025.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3829 : Certifies 3829 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0026.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3830 : Certifies 3830 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0027.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3831 : Certifies 3831 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0028.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3832 : Certifies 3832 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3833 : Certifies 3833 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0030.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3834 : Certifies 3834 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0031.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3835 : Certifies 3835 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0032.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3836 : Certifies 3836 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3837 : Certifies 3837 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3838 : Certifies 3838 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3839 : Certifies 3839 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3840 : Certifies 3840 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3841 : Certifies 3841 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3842 : Certifies 3842 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B126 (j : Fin 30) :
    Certifies (3813 + j.val) := by
  fin_cases j
  · exact projection_3813
  · exact projection_3814
  · exact projection_3815
  · exact projection_3816
  · exact projection_3817
  · exact projection_3818
  · exact projection_3819
  · exact projection_3820
  · exact projection_3821
  · exact projection_3822
  · exact projection_3823
  · exact projection_3824
  · exact projection_3825
  · exact projection_3826
  · exact projection_3827
  · exact projection_3828
  · exact projection_3829
  · exact projection_3830
  · exact projection_3831
  · exact projection_3832
  · exact projection_3833
  · exact projection_3834
  · exact projection_3835
  · exact projection_3836
  · exact projection_3837
  · exact projection_3838
  · exact projection_3839
  · exact projection_3840
  · exact projection_3841
  · exact projection_3842

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
