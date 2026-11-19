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
/- Source: ProjectionCertificates/R_one_six_1557.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1557

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 139, 805, 681, 961, 94, 198, 714, 308, 468, 632, 880, 7, 11, 131, 37, 261, 41, 137, 545, 385, 641, 769, 30, 70, 134, 74, 138, 194, 52, 84, 276, 292, 196, 388, 56, 88, 552, 584, 648, 624, 304, 336, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_139, vertices_805, vertices_681, vertices_961, vertices_94, vertices_198, vertices_714, vertices_308, vertices_468, vertices_632, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_138, vertices_194, vertices_52, vertices_84, vertices_276, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_648, vertices_624, vertices_304, vertices_336, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_139), (false, vertices_805), (false, vertices_681), (false, vertices_961), (true, vertices_70), (true, vertices_74), (true, vertices_194), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_88), (true, vertices_584), (true, vertices_624), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_624) then 19 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 8 624
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_2 2 0 1 2 3 30
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 74 714 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 468
cert_cover_5 4 3 1 3 5 6 84 468 3
cert_coverFacet 5 632
cert_cover_5 5 0 2 3 4 5 56 632 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 624 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1557

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1558.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1558

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 817, 465, 142, 714, 684, 964, 632, 848, 7, 27, 67, 131, 37, 261, 49, 81, 273, 801, 193, 385, 14, 134, 74, 138, 194, 44, 140, 548, 388, 644, 772, 56, 88, 552, 584, 648, 560, 336, 592, 784, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_817, vertices_465, vertices_142, vertices_714, vertices_684, vertices_964, vertices_632, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_273, vertices_801, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_648, vertices_560, vertices_336, vertices_592, vertices_784, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_817), (false, vertices_465), (true, vertices_138), (true, vertices_140), (true, vertices_644), (true, vertices_552), (true, vertices_584), (true, vertices_648), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 16 18 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 1 5 6 7 8 964 388 1
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 964
cert_cover_5 3 1 1 5 6 7 388 964 1
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1558

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1559.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1559

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 817, 465, 142, 714, 684, 964, 568, 856, 7, 27, 67, 131, 37, 261, 49, 81, 273, 801, 193, 385, 14, 134, 74, 138, 194, 44, 140, 548, 388, 644, 772, 56, 88, 536, 552, 584, 648, 560, 336, 784, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_817, vertices_465, vertices_142, vertices_714, vertices_684, vertices_964, vertices_568, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_273, vertices_801, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_648, vertices_560, vertices_336, vertices_784, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_817), (false, vertices_465), (true, vertices_138), (true, vertices_140), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_648), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 16 18 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 1 5 6 7 8 964 388 1
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 964
cert_cover_5 3 2 1 5 6 7 388 964 1
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1559

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1560.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1560

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 305, 465, 654, 714, 620, 900, 376, 992, 7, 27, 67, 131, 37, 261, 49, 81, 273, 289, 193, 385, 14, 134, 74, 650, 194, 44, 524, 548, 388, 644, 772, 56, 88, 104, 584, 304, 336, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_305, vertices_465, vertices_654, vertices_714, vertices_620, vertices_900, vertices_376, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_650, vertices_194, vertices_44, vertices_524, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_584, vertices_304, vertices_336, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_305), (false, vertices_465), (true, vertices_650), (true, vertices_524), (true, vertices_644), (true, vertices_104), (true, vertices_584), (true, vertices_352), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 10 19 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 12 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_465) then 16 else
  if p.val = (true, vertices_650) then 18 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1560

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1561.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1561

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 293, 817, 465, 654, 714, 812, 964, 632, 848, 7, 27, 67, 131, 37, 261, 49, 81, 273, 289, 193, 385, 14, 134, 74, 650, 194, 44, 524, 292, 388, 644, 772, 56, 88, 552, 584, 560, 336, 592, 784, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_293, vertices_817, vertices_465, vertices_654, vertices_714, vertices_812, vertices_964, vertices_632, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_650, vertices_194, vertices_44, vertices_524, vertices_292, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_560, vertices_336, vertices_592, vertices_784, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_293), (false, vertices_817), (false, vertices_465), (true, vertices_650), (true, vertices_524), (true, vertices_644), (true, vertices_772), (true, vertices_552), (true, vertices_584), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 10 20 14 12 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_817) then 13 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_650) then 19 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inl 4
  | 13 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 8 650
cert_row_4 1 1 5 6 7 8 964 388 1
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 964
cert_cover_5 3 1 1 5 6 7 388 964 1
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1561

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1562.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1562

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 293, 241, 929, 334, 450, 812, 696, 856, 976, 7, 27, 67, 131, 37, 261, 49, 81, 161, 289, 193, 385, 14, 262, 74, 194, 322, 386, 44, 268, 292, 56, 88, 536, 552, 328, 776, 176, 208, 848, 656, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_293, vertices_241, vertices_929, vertices_334, vertices_450, vertices_812, vertices_696, vertices_856, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_161, vertices_289, vertices_193, vertices_385, vertices_14, vertices_262, vertices_74, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_292, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_208, vertices_848, vertices_656, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_293), (false, vertices_241), (false, vertices_929), (true, vertices_322), (true, vertices_268), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_848), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 16 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_241) then 17 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_848) then 18 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_848), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
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
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 696
cert_cover_5 3 3 2 3 4 6 56 696 3
cert_coverFacet 4 856
cert_cover_5 4 1 2 3 5 7 88 856 3
cert_coverFacet 5 976
cert_cover_5 5 1 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1562

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1563.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1563

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 625, 961, 398, 202, 450, 300, 440, 728, 944, 7, 27, 67, 37, 261, 49, 81, 545, 321, 577, 769, 14, 262, 74, 138, 194, 322, 386, 44, 268, 292, 56, 88, 152, 296, 200, 392, 432, 560, 592, 656, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_625, vertices_961, vertices_398, vertices_202, vertices_450, vertices_300, vertices_440, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_292, vertices_56, vertices_88, vertices_152, vertices_296, vertices_200, vertices_392, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_625), (false, vertices_961), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_268), (true, vertices_152), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_432), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_625) then 17 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_656) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_rows_3
cert_pivot_3 0 4 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 88 728 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1563

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1564.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1564

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 294, 810, 436, 724, 632, 840, 944, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 262, 42, 266, 290, 52, 84, 148, 292, 196, 388, 56, 88, 552, 328, 584, 776, 432, 560, 592, 656, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_294, vertices_810, vertices_436, vertices_724, vertices_632, vertices_840, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_262, vertices_42, vertices_266, vertices_290, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_328, vertices_584, vertices_776, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_290), (true, vertices_148), (true, vertices_292), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_432) then 19 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_38 197 290 148 292 552 584 776 560 592 656 800 391 331 93 432
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 294
cert_cover_2 0 1 0 4 7 38 294 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 52 436 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1564

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1565.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1565

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 294, 810, 244, 932, 696, 728, 840, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 262, 42, 266, 290, 52, 84, 164, 292, 196, 388, 56, 88, 664, 552, 328, 584, 776, 176, 208, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_294, vertices_810, vertices_244, vertices_932, vertices_696, vertices_728, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_262, vertices_42, vertices_266, vertices_290, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_664, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_290), (true, vertices_164), (true, vertices_292), (true, vertices_664), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_176), (true, vertices_208), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_664) then 18 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 197 290 164 292 552 584 776 176 208 672 800 391 331 93 664
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 294
cert_cover_2 0 1 0 4 7 38 294 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 2 1 3 4 5 52 244 3
cert_coverFacet 3 932
cert_cover_5 3 3 1 4 6 7 164 932 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 728
cert_cover_5 5 1 2 3 5 6 88 728 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1565

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1566.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1566

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 294, 810, 244, 932, 568, 856, 752, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 262, 42, 266, 290, 52, 84, 164, 292, 196, 388, 56, 88, 536, 552, 328, 776, 240, 560, 592, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_294, vertices_810, vertices_244, vertices_932, vertices_568, vertices_856, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_262, vertices_42, vertices_266, vertices_290, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_240, vertices_560, vertices_592, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_290), (true, vertices_164), (true, vertices_292), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_38 197 290 164 292 536 552 776 560 592 672 800 391 331 93 240
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_4 1 1 4 6 7 8 932 164 3
cert_row_2 2 3 4 5 6 240
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 294
cert_cover_2 0 1 0 4 7 38 294 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 2 1 3 4 5 52 244 3
cert_coverFacet 3 932
cert_cover_5 3 1 1 4 6 7 164 932 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 752
cert_cover_5 6 2 3 4 5 8 240 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1566

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1567.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1567

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 294, 106, 866, 436, 724, 632, 944, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 262, 42, 74, 98, 290, 322, 52, 84, 148, 292, 196, 388, 56, 88, 104, 432, 560, 592, 656, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_294, vertices_106, vertices_866, vertices_436, vertices_724, vertices_632, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_262, vertices_42, vertices_74, vertices_98, vertices_290, vertices_322, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_104, vertices_432, vertices_560, vertices_592, vertices_656, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_98), (true, vertices_290), (true, vertices_148), (true, vertices_292), (true, vertices_104), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_432) then 19 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_38 197 98 290 148 292 104 560 592 656 608 800 391 331 93 432
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 5 7 8 866 98 3
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 294
cert_cover_2 0 1 0 4 7 38 294 3
cert_coverFacet 1 106
cert_cover_2 1 2 0 4 5 42 106 3
cert_coverFacet 2 866
cert_cover_5 2 0 0 4 5 7 98 866 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1567

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1568.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1568

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 587, 771, 93, 197, 961, 294, 810, 436, 724, 632, 944, 7, 11, 259, 515, 29, 69, 133, 73, 193, 577, 385, 769, 38, 262, 42, 522, 290, 770, 52, 84, 148, 292, 196, 388, 56, 88, 552, 584, 432, 560, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_587, vertices_771, vertices_93, vertices_197, vertices_961, vertices_294, vertices_810, vertices_436, vertices_724, vertices_632, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_42, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_587), (false, vertices_771), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_290), (true, vertices_148), (true, vertices_292), (true, vertices_552), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 294
cert_cover_2 0 1 0 4 7 38 294 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 52 436 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 944
cert_cover_5 5 1 3 4 6 8 432 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1568

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1569.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1569

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 587, 771, 93, 197, 961, 294, 810, 244, 932, 696, 728, 7, 11, 259, 515, 29, 69, 133, 73, 193, 577, 385, 769, 38, 262, 42, 522, 290, 770, 52, 84, 164, 292, 196, 388, 56, 88, 664, 552, 584, 176, 208, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_587, vertices_771, vertices_93, vertices_197, vertices_961, vertices_294, vertices_810, vertices_244, vertices_932, vertices_696, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_42, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_664, vertices_552, vertices_584, vertices_176, vertices_208, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_587), (false, vertices_771), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_290), (true, vertices_164), (true, vertices_292), (true, vertices_664), (true, vertices_552), (true, vertices_176), (true, vertices_208), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_664) then 17 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 294
cert_cover_2 0 1 0 4 7 38 294 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 2 1 3 4 5 52 244 3
cert_coverFacet 3 932
cert_cover_5 3 3 1 4 6 7 164 932 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 728
cert_cover_5 5 1 2 3 5 6 88 728 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1569

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1570.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1570

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 267, 677, 809, 961, 94, 198, 842, 450, 244, 696, 728, 7, 11, 259, 37, 133, 41, 265, 545, 385, 641, 769, 30, 70, 134, 74, 266, 194, 322, 386, 52, 84, 164, 196, 56, 88, 664, 552, 584, 776, 176, 208, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_267, vertices_677, vertices_809, vertices_961, vertices_94, vertices_198, vertices_842, vertices_450, vertices_244, vertices_696, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_37, vertices_133, vertices_41, vertices_265, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_266, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_664, vertices_552, vertices_584, vertices_776, vertices_176, vertices_208, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_267), (false, vertices_677), (false, vertices_809), (false, vertices_961), (true, vertices_70), (true, vertices_74), (true, vertices_194), (true, vertices_322), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_664), (true, vertices_584), (true, vertices_176), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_664) then 18 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_2 1 2 3 6 8 664
cert_row_2 2 0 1 2 3 30
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 8 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 244
cert_cover_5 4 3 1 3 4 5 52 244 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 728
cert_cover_5 6 1 2 3 5 6 88 728 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1570

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1571.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1571

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 677, 425, 94, 198, 450, 564, 724, 824, 856, 992, 7, 11, 259, 37, 133, 41, 265, 161, 385, 30, 70, 134, 74, 194, 322, 386, 52, 84, 532, 548, 196, 644, 56, 88, 792, 296, 328, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_677, vertices_425, vertices_94, vertices_198, vertices_450, vertices_564, vertices_724, vertices_824, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_37, vertices_133, vertices_41, vertices_265, vertices_161, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_792, vertices_296, vertices_328, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_677), (false, vertices_425), (true, vertices_70), (true, vertices_194), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_88), (true, vertices_792), (true, vertices_560), (true, vertices_592), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_792) then 20 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 2 3 7 8 792
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 856
cert_cover_5 6 1 2 3 5 7 88 856 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1571

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1572.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1572

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 677, 809, 897, 94, 198, 450, 244, 696, 856, 976, 7, 11, 259, 37, 133, 41, 265, 545, 385, 641, 769, 30, 70, 134, 74, 194, 322, 386, 52, 84, 164, 196, 56, 88, 536, 552, 328, 776, 176, 208, 848, 656, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_677, vertices_809, vertices_897, vertices_94, vertices_198, vertices_450, vertices_244, vertices_696, vertices_856, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_37, vertices_133, vertices_41, vertices_265, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_208, vertices_848, vertices_656, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_677), (false, vertices_809), (false, vertices_897), (true, vertices_70), (true, vertices_194), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_536), (true, vertices_176), (true, vertices_208), (true, vertices_848), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_848) then 20 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 897 70 194 84 196 88 536 176 208 656 448 391 331 677 809 848
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 3 5 7 8 848
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 52 244 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 56 696 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1572

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1573.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1573

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 267, 677, 809, 961, 94, 198, 458, 244, 568, 856, 752, 7, 11, 259, 37, 133, 41, 265, 545, 385, 641, 769, 30, 70, 134, 74, 266, 194, 386, 52, 84, 164, 196, 56, 88, 536, 552, 328, 776, 240, 560, 592, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_267, vertices_677, vertices_809, vertices_961, vertices_94, vertices_198, vertices_458, vertices_244, vertices_568, vertices_856, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_37, vertices_133, vertices_41, vertices_265, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_266, vertices_194, vertices_386, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_240, vertices_560, vertices_592, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_267), (false, vertices_677), (false, vertices_809), (false, vertices_961), (true, vertices_70), (true, vertices_74), (true, vertices_194), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_536), (true, vertices_328), (true, vertices_240), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_2 1 0 1 2 3 30
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 458
cert_cover_5 2 2 0 2 5 6 74 458 3
cert_coverFacet 3 244
cert_cover_5 3 0 1 3 4 5 52 244 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 752
cert_cover_5 6 0 3 4 5 8 240 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1573

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1574.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1574

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 267, 677, 809, 961, 94, 198, 458, 564, 724, 376, 880, 7, 11, 259, 37, 133, 41, 265, 545, 385, 641, 769, 30, 70, 134, 74, 266, 194, 386, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 368, 560, 592, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_267, vertices_677, vertices_809, vertices_961, vertices_94, vertices_198, vertices_458, vertices_564, vertices_724, vertices_376, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_37, vertices_133, vertices_41, vertices_265, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_266, vertices_194, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_368, vertices_560, vertices_592, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_267), (false, vertices_677), (false, vertices_809), (false, vertices_961), (true, vertices_70), (true, vertices_74), (true, vertices_194), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_88), (true, vertices_328), (true, vertices_368), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_368) then 19 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

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
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 8 368 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1574

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1575.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1575

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 93, 197, 457, 230, 554, 930, 628, 568, 856, 992, 7, 11, 259, 29, 69, 133, 73, 265, 193, 385, 38, 134, 42, 522, 162, 546, 386, 770, 52, 84, 100, 196, 56, 88, 536, 552, 328, 776, 560, 592, 224, 608, 928, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_93, vertices_197, vertices_457, vertices_230, vertices_554, vertices_930, vertices_628, vertices_568, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_162, vertices_546, vertices_386, vertices_770, vertices_52, vertices_84, vertices_100, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_592, vertices_224, vertices_608, vertices_928, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_93), (false, vertices_197), (false, vertices_457), (true, vertices_162), (true, vertices_546), (true, vertices_100), (true, vertices_536), (true, vertices_552), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_608), (true, vertices_928), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_928) then 21 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(true, vertices_928), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 6 230 38 3
cert_row_2 1 4 6 7 8 928
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 5 38 230 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 930
cert_cover_5 2 1 0 4 6 7 162 930 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1575

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1576.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1576

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 93, 197, 457, 678, 554, 962, 244, 568, 856, 752, 7, 11, 259, 29, 69, 133, 73, 265, 193, 385, 38, 134, 42, 522, 546, 386, 642, 770, 52, 84, 164, 196, 56, 88, 536, 552, 328, 776, 240, 560, 592, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_93, vertices_197, vertices_457, vertices_678, vertices_554, vertices_962, vertices_244, vertices_568, vertices_856, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_240, vertices_560, vertices_592, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_93), (false, vertices_197), (false, vertices_457), (true, vertices_546), (true, vertices_642), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_240) then 20 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 197 546 642 164 536 552 560 592 672 704 832 391 779 93 457 240
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 386 962 1
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 8 240 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1576

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1577.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1577

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 166, 426, 628, 740, 312, 856, 944, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 612, 164, 196, 56, 88, 280, 296, 328, 304, 560, 592, 784, 416, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_166, vertices_426, vertices_628, vertices_740, vertices_312, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_612), (true, vertices_164), (true, vertices_280), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_612) then 17 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 2 4 6 7 426 42 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 42 426 3
cert_coverFacet 2 628
cert_cover_5 2 0 1 3 4 5 52 628 3
cert_coverFacet 3 740
cert_cover_5 3 0 1 4 5 6 612 740 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1577

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1578.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1578

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 166, 426, 180, 724, 632, 872, 944, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 148, 164, 196, 56, 88, 616, 296, 328, 176, 560, 592, 656, 416, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_166, vertices_426, vertices_180, vertices_724, vertices_632, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_148, vertices_164, vertices_196, vertices_56, vertices_88, vertices_616, vertices_296, vertices_328, vertices_176, vertices_560, vertices_592, vertices_656, vertices_416, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_148), (true, vertices_164), (true, vertices_616), (true, vertices_296), (true, vertices_176), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_616) then 18 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 197 162 148 164 296 176 560 592 656 416 800 391 331 93 616
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 2 4 5 8 616
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 42 426 3
cert_coverFacet 2 180
cert_cover_2 2 3 1 4 6 52 180 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 632
cert_cover_5 4 1 2 3 4 5 56 632 3
cert_coverFacet 5 872
cert_cover_5 5 1 2 4 5 7 616 872 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1578

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1579.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1579

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 166, 426, 628, 740, 696, 856, 904, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 612, 164, 196, 56, 88, 536, 168, 328, 392, 648, 776, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_166, vertices_426, vertices_628, vertices_740, vertices_696, vertices_856, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_168, vertices_328, vertices_392, vertices_648, vertices_776, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_612), (true, vertices_164), (true, vertices_536), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_612) then 17 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 2 4 6 7 426 42 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 0 4 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 42 426 3
cert_coverFacet 2 628
cert_cover_5 2 0 1 3 4 5 52 628 3
cert_coverFacet 3 740
cert_cover_5 3 0 1 4 5 6 612 740 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1579

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1580.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1580

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 166, 170, 906, 628, 740, 696, 856, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 138, 266, 162, 386, 52, 84, 612, 164, 196, 56, 88, 536, 168, 328, 648, 776, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_166, vertices_170, vertices_906, vertices_628, vertices_740, vertices_696, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_138, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_168, vertices_328, vertices_648, vertices_776, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_138), (true, vertices_162), (true, vertices_612), (true, vertices_164), (true, vertices_536), (true, vertices_168), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_612) then 17 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 0 4 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 906
cert_cover_5 2 1 0 2 6 7 138 906 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 52 628 3
cert_coverFacet 4 740
cert_cover_5 4 0 1 4 5 6 612 740 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1580

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1581.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1581

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 166, 810, 930, 244, 696, 856, 720, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 802, 386, 52, 84, 164, 196, 56, 88, 536, 552, 328, 776, 176, 208, 592, 656, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_166, vertices_810, vertices_930, vertices_244, vertices_696, vertices_856, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_802, vertices_386, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_802), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_93) then 13 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_802) then 17 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_802), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
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
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 930
cert_cover_5 2 0 0 4 6 7 162 930 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1581

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1582.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1582

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 166, 810, 930, 180, 724, 696, 856, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 802, 386, 52, 84, 148, 164, 196, 56, 88, 536, 552, 328, 776, 176, 592, 656, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_166, vertices_810, vertices_930, vertices_180, vertices_724, vertices_696, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_802, vertices_386, vertices_52, vertices_84, vertices_148, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_592, vertices_656, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_802), (true, vertices_148), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_592), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_93) then 13 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_802) then 17 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_802), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 7 8 802
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 930
cert_cover_5 2 0 0 4 6 7 162 930 3
cert_coverFacet 3 180
cert_cover_2 3 3 1 4 6 52 180 3
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 6 84 724 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1582

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1583.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1583

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 426, 628, 708, 824, 856, 928, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 548, 196, 580, 644, 56, 88, 792, 296, 328, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_426, vertices_628, vertices_708, vertices_824, vertices_856, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_792, vertices_296, vertices_328, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_792), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_792) then 18 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 197 162 548 580 644 296 560 592 416 672 800 391 331 93 792
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
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1583

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1584.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1584

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 426, 628, 708, 568, 856, 936, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 548, 196, 580, 644, 56, 88, 536, 424, 552, 328, 776, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_426, vertices_628, vertices_708, vertices_568, vertices_856, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_536, vertices_424, vertices_552, vertices_328, vertices_776, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_536), (true, vertices_424), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_424) then 18 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 197 162 548 580 644 536 552 776 560 592 672 391 331 93 424
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
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 936
cert_cover_5 6 1 2 4 6 8 424 936 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1584

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1585.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1585

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 426, 564, 724, 824, 856, 928, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 532, 548, 196, 644, 56, 88, 792, 296, 328, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_426, vertices_564, vertices_724, vertices_824, vertices_856, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_792, vertices_296, vertices_328, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_792), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_792) then 18 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 197 162 532 548 644 296 560 592 416 672 800 391 331 93 792
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 8 724 84 3
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
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 0 1 3 5 6 84 724 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1585

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1586.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1586

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 426, 564, 724, 632, 872, 928, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 532, 548, 196, 644, 56, 88, 616, 296, 328, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_426, vertices_564, vertices_724, vertices_632, vertices_872, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_616, vertices_296, vertices_328, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_616), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_616) then 18 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 197 162 532 548 644 296 560 592 416 672 800 391 331 93 616
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 2 4 5 8 616
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 42 426 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 3 1 3 5 6 84 724 3
cert_coverFacet 4 632
cert_cover_5 4 1 2 3 4 5 56 632 3
cert_coverFacet 5 872
cert_cover_5 5 1 2 4 5 7 616 872 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1586

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1710 : Certifies 1710 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1557.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1711 : Certifies 1711 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1558.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1712 : Certifies 1712 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1559.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1713 : Certifies 1713 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1560.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1714 : Certifies 1714 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1561.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1715 : Certifies 1715 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1562.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1716 : Certifies 1716 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1563.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1717 : Certifies 1717 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1564.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1718 : Certifies 1718 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1565.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1719 : Certifies 1719 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1566.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1720 : Certifies 1720 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1567.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1721 : Certifies 1721 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1568.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1722 : Certifies 1722 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1569.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1723 : Certifies 1723 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1570.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1724 : Certifies 1724 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1571.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1725 : Certifies 1725 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1572.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1726 : Certifies 1726 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1573.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1727 : Certifies 1727 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1574.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1728 : Certifies 1728 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1575.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1729 : Certifies 1729 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1576.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1730 : Certifies 1730 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1577.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1731 : Certifies 1731 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1578.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1732 : Certifies 1732 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1579.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1733 : Certifies 1733 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1580.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1734 : Certifies 1734 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1581.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1735 : Certifies 1735 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1582.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1736 : Certifies 1736 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1583.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1737 : Certifies 1737 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1584.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1738 : Certifies 1738 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1585.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1739 : Certifies 1739 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1586.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B057 (j : Fin 30) :
    Certifies (1710 + j.val) := by
  fin_cases j
  · exact projection_1710
  · exact projection_1711
  · exact projection_1712
  · exact projection_1713
  · exact projection_1714
  · exact projection_1715
  · exact projection_1716
  · exact projection_1717
  · exact projection_1718
  · exact projection_1719
  · exact projection_1720
  · exact projection_1721
  · exact projection_1722
  · exact projection_1723
  · exact projection_1724
  · exact projection_1725
  · exact projection_1726
  · exact projection_1727
  · exact projection_1728
  · exact projection_1729
  · exact projection_1730
  · exact projection_1731
  · exact projection_1732
  · exact projection_1733
  · exact projection_1734
  · exact projection_1735
  · exact projection_1736
  · exact projection_1737
  · exact projection_1738
  · exact projection_1739

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
