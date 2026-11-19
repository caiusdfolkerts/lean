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
/- Source: ProjectionCertificates/R_one_six_1719.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1719

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 707, 677, 369, 865, 398, 202, 556, 780, 964, 824, 472, 7, 27, 67, 131, 37, 133, 49, 81, 353, 545, 577, 641, 14, 134, 74, 138, 194, 44, 268, 524, 548, 388, 644, 772, 56, 88, 280, 552, 200, 392, 776, 304, 336, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_707, vertices_677, vertices_369, vertices_865, vertices_398, vertices_202, vertices_556, vertices_780, vertices_964, vertices_824, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_353, vertices_545, vertices_577, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_268, vertices_524, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_552, vertices_200, vertices_392, vertices_776, vertices_304, vertices_336, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_707), (false, vertices_677), (false, vertices_369), (false, vertices_865), (true, vertices_138), (true, vertices_268), (true, vertices_524), (true, vertices_388), (true, vertices_772), (true, vertices_280), (true, vertices_552), (true, vertices_200), (true, vertices_392), (true, vertices_776), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 20 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_4 1 1 5 6 7 8 964 388 1
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 964
cert_cover_5 4 1 1 5 6 7 388 964 1
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1719

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1720.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1720

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 549, 773, 817, 465, 654, 714, 620, 900, 376, 992, 7, 27, 67, 131, 37, 261, 517, 49, 81, 273, 545, 193, 385, 769, 14, 134, 74, 650, 194, 44, 524, 548, 388, 644, 772, 56, 88, 104, 584, 304, 336, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_549, vertices_773, vertices_817, vertices_465, vertices_654, vertices_714, vertices_620, vertices_900, vertices_376, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_545, vertices_193, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_650, vertices_194, vertices_44, vertices_524, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_584, vertices_304, vertices_336, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_549), (false, vertices_773), (false, vertices_817), (false, vertices_465), (true, vertices_650), (true, vertices_524), (true, vertices_644), (true, vertices_104), (true, vertices_584), (true, vertices_352), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 11 21 15 13 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_773) then 2 else
  if p.val = (false, vertices_817) then 14 else
  if p.val = (false, vertices_465) then 18 else
  if p.val = (true, vertices_650) then 20 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inl 4
  | 14 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 8 650
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1720

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1721.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1721

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 433, 209, 654, 714, 620, 900, 376, 976, 864, 7, 27, 67, 131, 37, 261, 49, 81, 145, 289, 193, 385, 14, 134, 74, 650, 194, 44, 524, 548, 388, 644, 772, 56, 88, 104, 584, 304, 208, 336, 400, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_433, vertices_209, vertices_654, vertices_714, vertices_620, vertices_900, vertices_376, vertices_976, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_145, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_650, vertices_194, vertices_44, vertices_524, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_584, vertices_304, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_433), (false, vertices_209), (true, vertices_650), (true, vertices_524), (true, vertices_644), (true, vertices_104), (true, vertices_584), (true, vertices_336), (true, vertices_352), (true, vertices_608), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 12 21 15 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_433) then 18 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_650) then 20 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 8 650
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1721

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1722.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1722

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 293, 241, 929, 590, 838, 450, 812, 696, 600, 976, 7, 27, 67, 131, 37, 261, 49, 81, 161, 289, 193, 385, 14, 582, 262, 74, 194, 322, 386, 44, 524, 292, 772, 56, 88, 536, 552, 584, 176, 208, 592, 656, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_293, vertices_241, vertices_929, vertices_590, vertices_838, vertices_450, vertices_812, vertices_696, vertices_600, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_161, vertices_289, vertices_193, vertices_385, vertices_14, vertices_582, vertices_262, vertices_74, vertices_194, vertices_322, vertices_386, vertices_44, vertices_524, vertices_292, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_176, vertices_208, vertices_592, vertices_656, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_293), (false, vertices_241), (false, vertices_929), (true, vertices_582), (true, vertices_322), (true, vertices_524), (true, vertices_772), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_592), (true, vertices_656), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 12 14 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_241) then 16 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_582) then 19 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 582 838 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1722

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1723.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1723

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 293, 433, 721, 590, 838, 450, 812, 696, 600, 992, 7, 27, 67, 131, 37, 261, 49, 81, 145, 289, 193, 385, 14, 582, 262, 74, 194, 322, 386, 44, 524, 292, 772, 56, 88, 536, 552, 584, 176, 592, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_293, vertices_433, vertices_721, vertices_590, vertices_838, vertices_450, vertices_812, vertices_696, vertices_600, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_145, vertices_289, vertices_193, vertices_385, vertices_14, vertices_582, vertices_262, vertices_74, vertices_194, vertices_322, vertices_386, vertices_44, vertices_524, vertices_292, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_176, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_293), (false, vertices_433), (false, vertices_721), (true, vertices_582), (true, vertices_322), (true, vertices_524), (true, vertices_772), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 12 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 19 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_433) then 16 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (true, vertices_582) then 20 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 582 838 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1723

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1724.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1724

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 241, 929, 334, 962, 556, 780, 696, 856, 720, 7, 27, 67, 131, 37, 261, 49, 81, 161, 801, 193, 385, 14, 262, 74, 194, 322, 386, 44, 268, 524, 548, 772, 56, 88, 536, 552, 328, 776, 176, 208, 592, 656, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_241, vertices_929, vertices_334, vertices_962, vertices_556, vertices_780, vertices_696, vertices_856, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_161, vertices_801, vertices_193, vertices_385, vertices_14, vertices_262, vertices_74, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_524, vertices_548, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_241), (false, vertices_929), (true, vertices_322), (true, vertices_268), (true, vertices_524), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_592), (true, vertices_656), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 18 20 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 0 4 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1724

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1725.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1725

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 806, 810, 244, 676, 900, 696, 856, 720, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 262, 42, 266, 802, 52, 84, 164, 548, 196, 388, 644, 772, 56, 88, 536, 552, 328, 776, 176, 208, 592, 656, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_806, vertices_810, vertices_244, vertices_676, vertices_900, vertices_696, vertices_856, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_262, vertices_42, vertices_266, vertices_802, vertices_52, vertices_84, vertices_164, vertices_548, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_802), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_802) then 19 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_802), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 7 8 802
cert_row_4 1 1 3 4 5 6 244 52 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 38 806 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 1 1 3 4 5 52 244 3
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 900
cert_cover_2 4 6 1 7 8 388 900 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1725

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1726.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1726

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 806, 618, 834, 436, 212, 568, 728, 944, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 262, 42, 74, 546, 322, 578, 770, 52, 84, 148, 292, 196, 388, 56, 88, 536, 552, 584, 432, 560, 208, 656, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_806, vertices_618, vertices_834, vertices_436, vertices_212, vertices_568, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_262, vertices_42, vertices_74, vertices_546, vertices_322, vertices_578, vertices_770, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_432, vertices_560, vertices_208, vertices_656, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_148), (true, vertices_292), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_432), (true, vertices_560), (true, vertices_208), (true, vertices_656), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_432) then 21 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 197 546 578 770 148 292 536 552 584 560 208 656 800 391 331 93 432
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 38 3
cert_row_2 1 3 4 6 7 432
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 38 806 3
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 42 618 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 212
cert_cover_2 4 3 1 5 6 84 212 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 8 432 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1726

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1727.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1727

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 294, 618, 866, 436, 724, 696, 600, 928, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 262, 42, 74, 610, 290, 322, 52, 84, 148, 292, 196, 388, 56, 88, 536, 552, 584, 176, 592, 656, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_294, vertices_618, vertices_866, vertices_436, vertices_724, vertices_696, vertices_600, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_262, vertices_42, vertices_74, vertices_610, vertices_290, vertices_322, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_176, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_610), (true, vertices_290), (true, vertices_148), (true, vertices_292), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_176), (true, vertices_592), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_610) then 19 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_610), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 8 610
cert_row_4 1 1 3 4 6 7 436 52 3
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 294
cert_cover_2 0 1 0 4 7 38 294 3
cert_coverFacet 1 618
cert_cover_5 1 0 0 2 4 5 42 618 3
cert_coverFacet 2 866
cert_cover_5 2 0 0 4 5 7 610 866 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1727

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1728.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1728

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 241, 417, 334, 962, 556, 844, 568, 728, 944, 7, 27, 67, 131, 37, 261, 49, 81, 161, 289, 193, 385, 14, 262, 74, 194, 322, 386, 44, 332, 524, 548, 772, 56, 88, 536, 552, 584, 176, 560, 208, 656, 416, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_241, vertices_417, vertices_334, vertices_962, vertices_556, vertices_844, vertices_568, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_161, vertices_289, vertices_193, vertices_385, vertices_14, vertices_262, vertices_74, vertices_194, vertices_322, vertices_386, vertices_44, vertices_332, vertices_524, vertices_548, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_176, vertices_560, vertices_208, vertices_656, vertices_416, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_241), (false, vertices_417), (true, vertices_322), (true, vertices_332), (true, vertices_524), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_656), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_332) then 18 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 844
cert_cover_5 3 0 1 2 5 8 332 844 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 88 728 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1728

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1729.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1729

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 229, 625, 270, 202, 906, 300, 868, 964, 824, 728, 7, 27, 67, 131, 37, 133, 49, 81, 97, 193, 14, 262, 74, 138, 266, 194, 386, 44, 268, 100, 292, 196, 836, 388, 56, 88, 536, 296, 200, 648, 776, 560, 592, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_229, vertices_625, vertices_270, vertices_202, vertices_906, vertices_300, vertices_868, vertices_964, vertices_824, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_97, vertices_193, vertices_14, vertices_262, vertices_74, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_100, vertices_292, vertices_196, vertices_836, vertices_388, vertices_56, vertices_88, vertices_536, vertices_296, vertices_200, vertices_648, vertices_776, vertices_560, vertices_592, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_229), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_268), (true, vertices_292), (true, vertices_836), (true, vertices_536), (true, vertices_296), (true, vertices_200), (true, vertices_648), (true, vertices_776), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_836) then 19 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
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
cert_row_2 0 1 5 7 8 836
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 0 4 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 906
cert_cover_5 2 1 0 2 6 7 138 906 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 868
cert_cover_5 4 0 1 4 5 7 100 868 3
cert_coverFacet 5 964
cert_cover_5 5 0 1 5 6 7 196 964 3
cert_coverFacet 6 824
cert_cover_5 6 2 2 3 4 7 56 824 3
cert_coverFacet 7 728
cert_cover_5 7 3 2 3 5 6 88 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1729

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1730.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1730

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 677, 553, 961, 94, 198, 458, 244, 824, 344, 880, 736, 7, 11, 259, 37, 133, 41, 521, 545, 385, 641, 769, 30, 70, 134, 74, 266, 194, 386, 52, 84, 164, 196, 56, 88, 280, 552, 328, 776, 112, 816, 336, 224, 608, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_677, vertices_553, vertices_961, vertices_94, vertices_198, vertices_458, vertices_244, vertices_824, vertices_344, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_37, vertices_133, vertices_41, vertices_521, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_266, vertices_194, vertices_386, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_280, vertices_552, vertices_328, vertices_776, vertices_112, vertices_816, vertices_336, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_677), (false, vertices_553), (false, vertices_961), (true, vertices_70), (true, vertices_74), (true, vertices_194), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_280), (true, vertices_328), (true, vertices_112), (true, vertices_816), (true, vertices_336), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_816) then 21 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 553 70 74 194 84 196 88 280 328 112 336 224 608 391 779 677 816
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_2 2 0 1 2 3 30
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 8 7 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 244
cert_cover_5 3 3 1 3 4 5 52 244 3
cert_coverFacet 4 824
cert_cover_5 4 0 2 3 4 7 56 824 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 112 880 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1730

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1731.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1731

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 677, 553, 961, 94, 198, 458, 564, 724, 376, 808, 880, 7, 11, 259, 37, 133, 41, 521, 545, 385, 641, 769, 30, 70, 134, 74, 266, 194, 386, 52, 84, 532, 548, 196, 644, 56, 88, 296, 552, 328, 776, 368, 560, 592, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_677, vertices_553, vertices_961, vertices_94, vertices_198, vertices_458, vertices_564, vertices_724, vertices_376, vertices_808, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_37, vertices_133, vertices_41, vertices_521, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_266, vertices_194, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_368, vertices_560, vertices_592, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_677), (false, vertices_553), (false, vertices_961), (true, vertices_70), (true, vertices_74), (true, vertices_194), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_88), (true, vertices_296), (true, vertices_328), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_368) then 21 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 553 70 74 194 84 532 196 88 296 328 560 592 800 391 779 677 368
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 7 368
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_2 2 0 1 2 3 30
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 0 2 3 4 5 56 376 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 880
cert_cover_5 7 0 3 4 5 8 368 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1731

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1732.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1732

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 170, 394, 628, 708, 440, 856, 944, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 138, 266, 162, 386, 52, 84, 548, 196, 580, 644, 56, 88, 280, 168, 328, 392, 432, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_170, vertices_394, vertices_628, vertices_708, vertices_440, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_138, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_168, vertices_328, vertices_392, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_138), (true, vertices_162), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_432) then 21 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 197 138 162 548 580 644 280 168 392 560 592 784 672 391 331 93 432
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 440
cert_cover_5 5 1 2 3 4 6 56 440 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 8 432 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1732

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1733.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1733

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 426, 628, 708, 696, 344, 920, 848, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 548, 196, 580, 644, 56, 88, 664, 280, 168, 328, 392, 560, 336, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_426, vertices_628, vertices_708, vertices_696, vertices_344, vertices_920, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_664, vertices_280, vertices_168, vertices_328, vertices_392, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_664), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_664) then 20 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 2 3 6 8 664
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 42 426 3
cert_coverFacet 2 628
cert_cover_5 2 3 1 3 4 5 52 628 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 920
cert_cover_5 6 1 2 3 6 7 664 920 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1733

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1734.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1734

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 426, 628, 708, 184, 856, 920, 688, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 548, 196, 580, 644, 56, 88, 152, 792, 168, 328, 392, 176, 560, 592, 656, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_426, vertices_628, vertices_708, vertices_184, vertices_856, vertices_920, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_792, vertices_168, vertices_328, vertices_392, vertices_176, vertices_560, vertices_592, vertices_656, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_152), (true, vertices_792), (true, vertices_168), (true, vertices_392), (true, vertices_176), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_792) then 20 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 8 628 52 3
cert_row_2 1 2 3 7 8 792
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 0 2 4 6 7 426 42 3
cert_rows
cert_pivot_2 5 3 1 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 426
cert_cover_5 1 3 0 2 4 6 42 426 3
cert_coverFacet 2 628
cert_cover_5 2 0 1 3 4 5 52 628 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 920
cert_cover_5 6 1 2 3 6 7 152 920 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1734

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1735.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1735

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 426, 628, 708, 440, 856, 688, 912, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 548, 196, 580, 644, 56, 88, 280, 424, 328, 176, 560, 592, 400, 656, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_426, vertices_628, vertices_708, vertices_440, vertices_856, vertices_688, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_424, vertices_328, vertices_176, vertices_560, vertices_592, vertices_400, vertices_656, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_280), (true, vertices_424), (true, vertices_176), (true, vertices_560), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_424) then 20 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 2 4 6 7 424
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 42 426 3
cert_coverFacet 2 628
cert_cover_5 2 2 1 3 4 5 52 628 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1735

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1736.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1736

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 170, 394, 564, 724, 376, 936, 880, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 138, 266, 162, 386, 52, 84, 532, 548, 196, 644, 56, 88, 168, 296, 328, 392, 368, 560, 592, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_170, vertices_394, vertices_564, vertices_724, vertices_376, vertices_936, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_138, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_168, vertices_296, vertices_328, vertices_392, vertices_368, vertices_560, vertices_592, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_138), (true, vertices_162), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_368) then 21 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 197 138 162 532 548 644 168 296 392 560 592 672 800 391 331 93 368
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_2 2 3 4 5 7 368
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 2 2 3 4 5 56 376 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 168 936 3
cert_coverFacet 7 880
cert_cover_5 7 2 3 4 5 8 368 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1736

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1737.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1737

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 554, 906, 244, 824, 344, 880, 736, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 522, 546, 386, 642, 52, 84, 164, 196, 56, 88, 280, 552, 328, 776, 112, 816, 336, 224, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_554, vertices_906, vertices_244, vertices_824, vertices_344, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_522, vertices_546, vertices_386, vertices_642, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_280, vertices_552, vertices_328, vertices_776, vertices_112, vertices_816, vertices_336, vertices_224, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_522), (true, vertices_546), (true, vertices_642), (true, vertices_164), (true, vertices_280), (true, vertices_552), (true, vertices_776), (true, vertices_112), (true, vertices_816), (true, vertices_336), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_816) then 21 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 197 522 546 642 164 280 552 776 112 336 224 608 672 391 331 93 816
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 266 2
cert_row_2 1 3 4 7 8 816
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 906
cert_cover_5 2 0 0 2 6 7 266 906 2
cert_coverFacet 3 244
cert_cover_5 3 3 1 3 4 5 52 244 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 880
cert_cover_5 6 1 3 4 5 7 112 880 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1737

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1738.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1738

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 554, 906, 564, 724, 376, 808, 880, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 522, 546, 386, 642, 52, 84, 532, 548, 196, 644, 56, 88, 296, 552, 328, 776, 368, 560, 592, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_554, vertices_906, vertices_564, vertices_724, vertices_376, vertices_808, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_522, vertices_546, vertices_386, vertices_642, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_368, vertices_560, vertices_592, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_522), (true, vertices_546), (true, vertices_642), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_368) then 21 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 197 522 546 642 532 548 644 296 552 776 560 592 800 391 331 93 368
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 266 2
cert_row_2 1 3 4 5 7 368
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 906
cert_cover_5 2 0 0 2 6 7 266 906 2
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 1 2 3 4 5 56 376 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 880
cert_cover_5 7 1 3 4 5 8 368 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1738

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1739.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1739

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 689, 849, 398, 202, 962, 556, 908, 248, 680, 720, 7, 27, 67, 37, 261, 49, 81, 529, 545, 321, 769, 14, 262, 74, 138, 194, 322, 386, 44, 396, 524, 548, 772, 56, 88, 168, 552, 200, 648, 176, 208, 592, 656, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_689, vertices_849, vertices_398, vertices_202, vertices_962, vertices_556, vertices_908, vertices_248, vertices_680, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_524, vertices_548, vertices_772, vertices_56, vertices_88, vertices_168, vertices_552, vertices_200, vertices_648, vertices_176, vertices_208, vertices_592, vertices_656, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_689), (false, vertices_849), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_524), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_208), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 908
cert_cover_5 4 0 1 2 6 8 396 908 3
cert_coverFacet 5 248
cert_cover_5 5 2 2 3 4 5 56 248 3
cert_coverFacet 6 680
cert_cover_2 6 4 2 6 8 168 680 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1739

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1740.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1740

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 525, 597, 809, 369, 961, 398, 534, 902, 122, 202, 722, 780, 488, 13, 21, 517, 41, 521, 49, 81, 289, 321, 577, 769, 14, 22, 390, 518, 58, 74, 138, 82, 530, 194, 642, 268, 524, 532, 772, 104, 296, 200, 392, 776, 112, 592, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_525, vertices_597, vertices_809, vertices_369, vertices_961, vertices_398, vertices_534, vertices_902, vertices_122, vertices_202, vertices_722, vertices_780, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_41, vertices_521, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_390, vertices_518, vertices_58, vertices_74, vertices_138, vertices_82, vertices_530, vertices_194, vertices_642, vertices_268, vertices_524, vertices_532, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_776, vertices_112, vertices_592, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_525), (false, vertices_597), (false, vertices_809), (false, vertices_369), (false, vertices_961), (true, vertices_390), (true, vertices_518), (true, vertices_74), (true, vertices_138), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_268), (true, vertices_772), (true, vertices_104), (true, vertices_200), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_390) then 14 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 902
cert_cover_5 2 0 0 1 6 8 390 902 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 5 58 122 3
cert_coverFacet 4 202
cert_cover_2 4 2 0 5 6 74 202 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 6 82 722 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1740

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1741.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1741

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 195, 899, 421, 773, 241, 590, 706, 812, 440, 856, 976, 7, 27, 67, 131, 515, 37, 261, 517, 49, 81, 161, 193, 385, 769, 14, 518, 74, 194, 578, 642, 44, 524, 292, 772, 56, 88, 280, 296, 584, 776, 176, 208, 848, 400, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_195, vertices_899, vertices_421, vertices_773, vertices_241, vertices_590, vertices_706, vertices_812, vertices_440, vertices_856, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_515, vertices_37, vertices_261, vertices_517, vertices_49, vertices_81, vertices_161, vertices_193, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_292, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_208, vertices_848, vertices_400, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_195), (false, vertices_899), (false, vertices_421), (false, vertices_773), (false, vertices_241), (true, vertices_578), (true, vertices_524), (true, vertices_280), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_848), (true, vertices_400), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_773) then 2 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_848) then 20 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_848), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_2 1 3 5 7 8 848
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 440
cert_cover_5 3 3 2 3 4 6 56 440 3
cert_coverFacet 4 856
cert_cover_5 4 1 2 3 5 7 88 856 3
cert_coverFacet 5 976
cert_cover_5 5 1 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1741

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1742.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1742

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 195, 899, 805, 369, 449, 206, 646, 684, 824, 728, 976, 7, 27, 67, 131, 515, 37, 517, 49, 81, 289, 193, 321, 385, 769, 14, 134, 518, 74, 194, 642, 44, 140, 548, 644, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_195, vertices_899, vertices_805, vertices_369, vertices_449, vertices_206, vertices_646, vertices_684, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_193, vertices_321, vertices_385, vertices_769, vertices_14, vertices_134, vertices_518, vertices_74, vertices_194, vertices_642, vertices_44, vertices_140, vertices_548, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_195), (false, vertices_899), (false, vertices_805), (false, vertices_369), (false, vertices_449), (true, vertices_134), (true, vertices_140), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_720), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_449) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_720) then 20 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 824
cert_cover_5 3 3 2 3 4 7 56 824 3
cert_coverFacet 4 728
cert_cover_5 4 1 2 3 5 6 88 728 3
cert_coverFacet 5 976
cert_cover_5 5 1 3 5 6 7 720 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1742

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1743.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1743

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 195, 899, 805, 305, 465, 206, 646, 684, 632, 968, 880, 7, 27, 67, 131, 515, 37, 517, 49, 81, 273, 289, 193, 385, 769, 14, 134, 518, 74, 194, 642, 44, 140, 548, 644, 56, 88, 552, 200, 584, 648, 624, 304, 336, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_195, vertices_899, vertices_805, vertices_305, vertices_465, vertices_206, vertices_646, vertices_684, vertices_632, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_385, vertices_769, vertices_14, vertices_134, vertices_518, vertices_74, vertices_194, vertices_642, vertices_44, vertices_140, vertices_548, vertices_644, vertices_56, vertices_88, vertices_552, vertices_200, vertices_584, vertices_648, vertices_624, vertices_304, vertices_336, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_195), (false, vertices_899), (false, vertices_805), (false, vertices_305), (false, vertices_465), (true, vertices_134), (true, vertices_140), (true, vertices_644), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_624), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_305) then 2 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_624) then 20 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 8 624
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 632
cert_cover_5 3 0 2 3 4 5 56 632 3
cert_coverFacet 4 968
cert_cover_5 4 3 2 5 6 7 200 968 3
cert_coverFacet 5 880
cert_cover_5 5 0 3 4 5 7 624 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1743

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1744.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1744

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 195, 899, 677, 241, 334, 774, 450, 812, 696, 856, 976, 7, 27, 67, 131, 515, 37, 517, 49, 81, 161, 193, 641, 14, 262, 518, 74, 194, 322, 386, 770, 44, 268, 548, 772, 56, 88, 536, 552, 328, 776, 176, 208, 848, 656, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_195, vertices_899, vertices_677, vertices_241, vertices_334, vertices_774, vertices_450, vertices_812, vertices_696, vertices_856, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_161, vertices_193, vertices_641, vertices_14, vertices_262, vertices_518, vertices_74, vertices_194, vertices_322, vertices_386, vertices_770, vertices_44, vertices_268, vertices_548, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_208, vertices_848, vertices_656, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_195), (false, vertices_899), (false, vertices_677), (false, vertices_241), (true, vertices_262), (true, vertices_322), (true, vertices_268), (true, vertices_772), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_848), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_848) then 21 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_848), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_2 1 3 5 7 8 848
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 56 696 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1744

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1745.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1745

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 526, 202, 906, 962, 428, 780, 248, 464, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 518, 74, 138, 522, 194, 578, 898, 44, 268, 524, 292, 772, 56, 88, 168, 200, 392, 776, 176, 208, 336, 400, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_526, vertices_202, vertices_906, vertices_962, vertices_428, vertices_780, vertices_248, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_138, vertices_522, vertices_194, vertices_578, vertices_898, vertices_44, vertices_268, vertices_524, vertices_292, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_392, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_898), (true, vertices_268), (true, vertices_524), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_776), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 11 14 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_898) then 18 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 6 7 8 898
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_rows_3
cert_pivot_3 1 0 2
cert_heightProof 3
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 906
cert_cover_5 2 0 0 2 6 7 138 906 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 7 194 962 3
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 44 428 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 56 248 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1745

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1747.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1747

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 91, 195, 899, 421, 241, 590, 706, 812, 440, 856, 720, 912, 7, 27, 67, 131, 771, 37, 261, 49, 81, 161, 193, 385, 14, 518, 74, 194, 578, 642, 44, 524, 292, 772, 56, 88, 280, 296, 584, 776, 176, 208, 592, 400, 656, 784, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_91, vertices_195, vertices_899, vertices_421, vertices_241, vertices_590, vertices_706, vertices_812, vertices_440, vertices_856, vertices_720, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_771, vertices_37, vertices_261, vertices_49, vertices_81, vertices_161, vertices_193, vertices_385, vertices_14, vertices_518, vertices_74, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_292, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_91), (false, vertices_195), (false, vertices_899), (false, vertices_421), (false, vertices_241), (true, vertices_578), (true, vertices_524), (true, vertices_280), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 14 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_899) then 19 else
  if p.val = (false, vertices_421) then 13 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 440
cert_cover_5 3 2 2 3 4 6 56 440 3
cert_coverFacet 4 856
cert_cover_5 4 3 2 3 5 7 88 856 3
cert_coverFacet 5 720
cert_cover_2 5 5 3 6 8 208 720 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1747

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1748.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1748

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 91, 195, 899, 421, 241, 590, 706, 812, 440, 856, 464, 960, 7, 27, 67, 131, 771, 37, 261, 49, 81, 161, 193, 385, 14, 518, 74, 194, 578, 642, 44, 524, 292, 772, 56, 88, 280, 296, 584, 776, 176, 208, 336, 400, 416, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_91, vertices_195, vertices_899, vertices_421, vertices_241, vertices_590, vertices_706, vertices_812, vertices_440, vertices_856, vertices_464, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_771, vertices_37, vertices_261, vertices_49, vertices_81, vertices_161, vertices_193, vertices_385, vertices_14, vertices_518, vertices_74, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_292, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_91), (false, vertices_195), (false, vertices_899), (false, vertices_421), (false, vertices_241), (true, vertices_578), (true, vertices_524), (true, vertices_280), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_336), (true, vertices_400), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 14 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_899) then 19 else
  if p.val = (false, vertices_421) then 13 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 440
cert_cover_5 3 2 2 3 4 6 56 440 3
cert_coverFacet 4 856
cert_cover_5 4 3 2 3 5 7 88 856 3
cert_coverFacet 5 464
cert_cover_2 5 5 3 6 7 208 464 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1748

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1749.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1749

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 678, 170, 564, 468, 916, 632, 936, 848, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 138, 162, 52, 84, 404, 532, 548, 196, 644, 56, 88, 168, 552, 584, 392, 776, 560, 336, 592, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_678, vertices_170, vertices_564, vertices_468, vertices_916, vertices_632, vertices_936, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_138, vertices_162, vertices_52, vertices_84, vertices_404, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_168, vertices_552, vertices_584, vertices_392, vertices_776, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_162), (true, vertices_404), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_168), (true, vertices_552), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 20 16 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_404) then 21 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 3 6 7 404
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 8 404 916 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 168 936 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1749

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1860 : Certifies 1860 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1719.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1861 : Certifies 1861 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1720.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1862 : Certifies 1862 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1721.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1863 : Certifies 1863 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1722.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1864 : Certifies 1864 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1723.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1865 : Certifies 1865 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1724.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1866 : Certifies 1866 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1725.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1867 : Certifies 1867 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1726.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1868 : Certifies 1868 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1727.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1869 : Certifies 1869 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1728.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1870 : Certifies 1870 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1729.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1871 : Certifies 1871 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1730.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1872 : Certifies 1872 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1731.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1873 : Certifies 1873 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1732.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1874 : Certifies 1874 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1733.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1875 : Certifies 1875 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1734.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1876 : Certifies 1876 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1735.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1877 : Certifies 1877 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1736.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1878 : Certifies 1878 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1737.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1879 : Certifies 1879 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1738.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1880 : Certifies 1880 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1739.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1881 : Certifies 1881 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1740.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1882 : Certifies 1882 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1741.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1883 : Certifies 1883 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1742.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1884 : Certifies 1884 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1743.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1885 : Certifies 1885 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1744.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1886 : Certifies 1886 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1745.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1887 : Certifies 1887 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1747.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1888 : Certifies 1888 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1748.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1889 : Certifies 1889 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1749.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B062 (j : Fin 30) :
    Certifies (1860 + j.val) := by
  fin_cases j
  · exact projection_1860
  · exact projection_1861
  · exact projection_1862
  · exact projection_1863
  · exact projection_1864
  · exact projection_1865
  · exact projection_1866
  · exact projection_1867
  · exact projection_1868
  · exact projection_1869
  · exact projection_1870
  · exact projection_1871
  · exact projection_1872
  · exact projection_1873
  · exact projection_1874
  · exact projection_1875
  · exact projection_1876
  · exact projection_1877
  · exact projection_1878
  · exact projection_1879
  · exact projection_1880
  · exact projection_1881
  · exact projection_1882
  · exact projection_1883
  · exact projection_1884
  · exact projection_1885
  · exact projection_1886
  · exact projection_1887
  · exact projection_1888
  · exact projection_1889

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
