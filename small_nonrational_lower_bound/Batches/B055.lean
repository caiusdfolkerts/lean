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
/- Source: ProjectionCertificates/R_one_six_1496.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1496

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 451, 805, 369, 897, 206, 684, 824, 728, 976, 7, 27, 67, 131, 37, 517, 49, 81, 289, 321, 385, 641, 769, 14, 134, 74, 194, 44, 140, 548, 644, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_451, vertices_805, vertices_369, vertices_897, vertices_206, vertices_684, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_548, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_451), (false, vertices_805), (false, vertices_369), (false, vertices_897), (true, vertices_140), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_720), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 7 14 15 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_647) then 8 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_805) then 9 else
  if p.val = (false, vertices_369) then 16 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_720) then 17 else
  if p.val = (true, vertices_784) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inl 1
  | 8 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
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
cert_coverFacet 1 684
cert_cover_5 1 2 1 2 4 6 44 684 3
cert_coverFacet 2 824
cert_cover_5 2 3 2 3 4 7 56 824 3
cert_coverFacet 3 728
cert_cover_5 3 1 2 3 5 6 88 728 3
cert_coverFacet 4 976
cert_cover_5 4 1 3 5 6 7 720 976 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1496

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1498.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1498

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 142, 458, 812, 908, 376, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 138, 194, 44, 140, 780, 548, 644, 56, 88, 296, 328, 392, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_142, vertices_458, vertices_812, vertices_908, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_780, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_138), (true, vertices_140), (true, vertices_780), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_677) then 13 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_780) then 14 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_2 1 3 5 6 8 720
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 2 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 908
cert_cover_5 3 0 1 2 6 7 140 908 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 976
cert_cover_5 5 1 3 5 6 7 720 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1498

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1499.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1499

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 421, 809, 94, 458, 692, 724, 568, 856, 992, 7, 11, 131, 37, 133, 41, 265, 289, 385, 30, 70, 74, 394, 194, 52, 84, 660, 164, 196, 56, 88, 536, 552, 328, 776, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_421, vertices_809, vertices_94, vertices_458, vertices_692, vertices_724, vertices_568, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_133, vertices_41, vertices_265, vertices_289, vertices_385, vertices_30, vertices_70, vertices_74, vertices_394, vertices_194, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_421), (false, vertices_809), (true, vertices_74), (true, vertices_84), (true, vertices_660), (true, vertices_88), (true, vertices_536), (true, vertices_328), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_660) then 17 else
  if p.val = (true, vertices_88) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 4 5 6 7 8 992 416 1
cert_row_4 1 2 3 5 7 8 856 88 3
cert_row_2 2 0 2 6 7 394
cert_row_2 3 0 1 2 3 30
cert_row_2 4 1 3 6 8 660
cert_rows_2
cert_pivot 4 5 7 0 1
cert_heightProof 5
cert_coverFacet 0 94
cert_cover_5 0 3 0 1 2 5 30 94 3
cert_coverFacet 1 458
cert_cover_5 1 2 0 2 5 6 74 458 3
cert_coverFacet 2 692
cert_cover_5 2 4 1 3 4 6 52 692 3
cert_coverFacet 3 724
cert_cover_5 3 4 1 3 5 6 84 724 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1499

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1500.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1500

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 398, 458, 812, 900, 376, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 394, 194, 44, 268, 548, 388, 644, 772, 56, 88, 296, 328, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_398, vertices_458, vertices_812, vertices_900, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_394, vertices_194, vertices_44, vertices_268, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_394), (true, vertices_268), (true, vertices_388), (true, vertices_772), (true, vertices_296), (true, vertices_328), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 8 19 13 11 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_677) then 10 else
  if p.val = (false, vertices_817) then 12 else
  if p.val = (false, vertices_721) then 16 else
  if p.val = (true, vertices_394) then 18 else
  if p.val = (true, vertices_268) then 0 else
  if p.val = (true, vertices_388) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 11 => Sum.inl 4
  | 12 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 976
cert_cover_5 5 1 3 5 6 7 720 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1500

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1501.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1501

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 151, 899, 597, 113, 433, 865, 126, 186, 394, 778, 844, 488, 7, 131, 515, 21, 517, 49, 81, 145, 97, 289, 577, 385, 769, 14, 22, 58, 138, 266, 522, 146, 386, 770, 76, 524, 84, 580, 104, 168, 328, 392, 776, 112, 176, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_151, vertices_899, vertices_597, vertices_113, vertices_433, vertices_865, vertices_126, vertices_186, vertices_394, vertices_778, vertices_844, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_515, vertices_21, vertices_517, vertices_49, vertices_81, vertices_145, vertices_97, vertices_289, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_58, vertices_138, vertices_266, vertices_522, vertices_146, vertices_386, vertices_770, vertices_76, vertices_524, vertices_84, vertices_580, vertices_104, vertices_168, vertices_328, vertices_392, vertices_776, vertices_112, vertices_176, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_151), (false, vertices_899), (false, vertices_597), (false, vertices_113), (false, vertices_433), (false, vertices_865), (true, vertices_58), (true, vertices_138), (true, vertices_266), (true, vertices_76), (true, vertices_104), (true, vertices_168), (true, vertices_328), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 9 16 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 10 else
  if p.val = (false, vertices_151) then 11 else
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_597) then 12 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_433) then 18 else
  if p.val = (false, vertices_865) then 20 else
  if p.val = (true, vertices_58) then 15 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_776) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 7 8 844 76 3
cert_row_4 1 2 4 5 6 7 488 104 3
cert_row_4 2 0 1 2 3 4 126 14 3
cert_row_4 3 0 1 2 3 5 126 14 3
cert_rows
cert_pivot_2 8 6 4 0
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 186
cert_cover 1 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 844
cert_cover_5 4 0 1 2 5 7 76 844 3
cert_coverFacet 5 488
cert_cover_5 5 1 2 4 5 6 104 488 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1501

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1502.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1502

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 721, 897, 782, 202, 394, 962, 428, 248, 7, 27, 67, 37, 517, 49, 81, 145, 289, 577, 385, 641, 769, 14, 518, 74, 138, 266, 194, 578, 386, 770, 44, 268, 292, 772, 56, 88, 168, 200, 392, 176, 208, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_721, vertices_897, vertices_782, vertices_202, vertices_394, vertices_962, vertices_428, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_145, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_138, vertices_266, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_268, vertices_292, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_392, vertices_176, vertices_208, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_721), (false, vertices_897), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_168), (true, vertices_200), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_583) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_433) then 18 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_392) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 6 248 56 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 428
cert_cover_5 4 3 1 2 4 6 44 428 3
cert_coverFacet 5 248
cert_cover_5 5 0 2 3 4 5 56 248 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1502

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1503.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1503

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 782, 202, 394, 962, 428, 248, 464, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 518, 74, 138, 266, 194, 578, 386, 770, 44, 268, 292, 772, 56, 88, 168, 200, 392, 176, 208, 336, 400, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_782, vertices_202, vertices_394, vertices_962, vertices_428, vertices_248, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_138, vertices_266, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_268, vertices_292, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_392, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 266 194 386 770 268 168 200 392 208 448 583 91 63 805 433 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 6 248 56 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 428
cert_cover_5 4 3 1 2 4 6 44 428 3
cert_coverFacet 5 248
cert_cover_5 5 0 2 3 4 5 56 248 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1503

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1504.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1504

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 689, 849, 398, 202, 962, 300, 248, 936, 720, 7, 27, 67, 37, 261, 49, 81, 529, 545, 321, 769, 14, 262, 74, 138, 194, 322, 386, 44, 268, 292, 56, 88, 168, 296, 200, 392, 176, 208, 592, 656, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_689, vertices_849, vertices_398, vertices_202, vertices_962, vertices_300, vertices_248, vertices_936, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_292, vertices_56, vertices_88, vertices_168, vertices_296, vertices_200, vertices_392, vertices_176, vertices_208, vertices_592, vertices_656, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_689), (false, vertices_849), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_268), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_208), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 194 386 268 168 296 200 392 208 704 896 327 91 63 805 689 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 248
cert_cover_5 4 2 2 3 4 5 56 248 3
cert_coverFacet 5 936
cert_cover_5 5 3 2 4 6 7 168 936 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1504

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1505.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1505

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 151, 899, 341, 113, 689, 865, 126, 186, 394, 844, 744, 904, 7, 131, 259, 21, 261, 49, 81, 145, 97, 545, 321, 641, 769, 14, 22, 58, 138, 266, 146, 386, 76, 268, 84, 324, 104, 168, 584, 392, 648, 776, 112, 176, 608, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_151, vertices_899, vertices_341, vertices_113, vertices_689, vertices_865, vertices_126, vertices_186, vertices_394, vertices_844, vertices_744, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_259, vertices_21, vertices_261, vertices_49, vertices_81, vertices_145, vertices_97, vertices_545, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_58, vertices_138, vertices_266, vertices_146, vertices_386, vertices_76, vertices_268, vertices_84, vertices_324, vertices_104, vertices_168, vertices_584, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_608, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_151), (false, vertices_899), (false, vertices_341), (false, vertices_113), (false, vertices_689), (false, vertices_865), (true, vertices_58), (true, vertices_138), (true, vertices_76), (true, vertices_104), (true, vertices_168), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 9 16 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 10 else
  if p.val = (false, vertices_151) then 11 else
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (false, vertices_865) then 20 else
  if p.val = (true, vertices_58) then 15 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 7 8 844 76 3
cert_row_4 1 2 4 5 6 8 744 104 3
cert_row_4 2 0 1 2 3 4 126 14 3
cert_row_4 3 0 1 2 3 5 126 14 3
cert_rows
cert_pivot_2 7 6 4 0
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 186
cert_cover 1 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 844
cert_cover_5 3 0 1 2 5 7 76 844 3
cert_coverFacet 4 744
cert_cover_5 4 1 2 4 5 6 104 744 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1505

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1506.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1506

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 421, 689, 849, 897, 398, 202, 962, 684, 632, 712, 7, 27, 67, 37, 261, 49, 81, 529, 161, 321, 385, 641, 769, 14, 262, 74, 138, 194, 322, 386, 44, 140, 164, 388, 56, 88, 552, 200, 584, 648, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_421, vertices_689, vertices_849, vertices_897, vertices_398, vertices_202, vertices_962, vertices_684, vertices_632, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_164, vertices_388, vertices_56, vertices_88, vertices_552, vertices_200, vertices_584, vertices_648, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_421), (false, vertices_689), (false, vertices_849), (false, vertices_897), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_327) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 8 632 56 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 2 6 7 398 14 3
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 3 1 2 4 6 44 684 3
cert_coverFacet 4 632
cert_cover_5 4 0 2 3 4 5 56 632 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1506

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1507.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1507

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 689, 849, 398, 202, 962, 684, 900, 248, 720, 7, 27, 67, 37, 261, 49, 81, 529, 545, 321, 769, 14, 262, 74, 138, 194, 322, 386, 44, 140, 548, 388, 644, 772, 56, 88, 168, 200, 176, 208, 592, 656, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_689, vertices_849, vertices_398, vertices_202, vertices_962, vertices_684, vertices_900, vertices_248, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_176, vertices_208, vertices_592, vertices_656, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_689), (false, vertices_849), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_388), (true, vertices_644), (true, vertices_168), (true, vertices_200), (true, vertices_208), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 194 386 140 388 644 168 200 208 704 896 327 91 63 805 689 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 6 248 56 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 2 6 7 398 14 3
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 3 1 2 4 6 44 684 3
cert_coverFacet 4 900
cert_cover_2 4 6 1 7 8 388 900 3
cert_coverFacet 5 248
cert_cover_5 5 0 2 3 4 5 56 248 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1507

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1508.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1508

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 805, 625, 206, 450, 428, 184, 728, 944, 960, 7, 27, 67, 259, 37, 261, 49, 81, 545, 577, 769, 14, 134, 74, 194, 322, 386, 44, 140, 292, 388, 56, 88, 152, 168, 200, 176, 560, 592, 656, 416, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_805, vertices_625, vertices_206, vertices_450, vertices_428, vertices_184, vertices_728, vertices_944, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_577, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_292, vertices_388, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_560, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_625), (true, vertices_194), (true, vertices_140), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_656), (true, vertices_416), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (true, vertices_194) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 194 1 140 152 168 200 176 656 416 448 704 896 391 805 91 835 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 428
cert_cover_5 2 1 1 2 4 6 44 428 3
cert_coverFacet 3 184
cert_cover_2 3 3 2 4 6 56 184 3
cert_coverFacet 4 728
cert_cover_5 4 2 2 3 5 6 88 728 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1508

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1509.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1509

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 421, 817, 721, 897, 398, 842, 450, 812, 632, 960, 7, 27, 67, 37, 133, 49, 81, 529, 289, 193, 385, 641, 769, 14, 134, 74, 266, 194, 322, 386, 44, 268, 292, 388, 56, 88, 552, 584, 776, 560, 592, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_421, vertices_817, vertices_721, vertices_897, vertices_398, vertices_842, vertices_450, vertices_812, vertices_632, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_289, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_560, vertices_592, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_421), (false, vertices_817), (false, vertices_721), (false, vertices_897), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_268), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 74 842 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 960
cert_cover_2 5 6 5 7 8 448 960 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1509

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1510.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1510

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 805, 369, 206, 450, 898, 684, 184, 472, 944, 7, 27, 67, 515, 37, 517, 49, 81, 289, 321, 769, 14, 134, 74, 194, 322, 386, 642, 770, 44, 140, 548, 644, 56, 88, 152, 168, 200, 176, 304, 336, 400, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_805, vertices_369, vertices_206, vertices_450, vertices_898, vertices_684, vertices_184, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_548, vertices_644, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_369), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_194) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 194 1 386 140 152 168 200 176 400 672 448 896 647 805 91 835 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1510

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1511.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1511

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 465, 897, 654, 842, 450, 898, 812, 376, 7, 27, 67, 37, 133, 49, 81, 273, 545, 193, 385, 641, 769, 14, 134, 74, 522, 194, 322, 386, 642, 770, 44, 524, 548, 644, 56, 88, 296, 328, 776, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_465, vertices_897, vertices_654, vertices_842, vertices_450, vertices_898, vertices_812, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_273, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_465), (false, vertices_897), (true, vertices_522), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_776) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 74 842 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 44 812 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1511

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1512.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1512

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 331, 899, 677, 809, 94, 198, 450, 244, 696, 856, 976, 7, 11, 131, 259, 37, 133, 41, 265, 545, 641, 769, 30, 70, 134, 74, 194, 322, 386, 52, 84, 164, 196, 56, 88, 536, 552, 328, 776, 176, 208, 848, 656, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_331, vertices_899, vertices_677, vertices_809, vertices_94, vertices_198, vertices_450, vertices_244, vertices_696, vertices_856, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_37, vertices_133, vertices_41, vertices_265, vertices_545, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_208, vertices_848, vertices_656, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_331), (false, vertices_899), (false, vertices_677), (false, vertices_809), (true, vertices_70), (true, vertices_194), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_536), (true, vertices_176), (true, vertices_208), (true, vertices_848), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_809) then 18 else
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
cert_nodeAtPriority_18 135 70 194 84 196 88 536 176 208 656 448 331 899 677 809 848
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1512

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1513.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1513

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 331, 899, 677, 809, 94, 198, 450, 820, 724, 376, 976, 7, 11, 131, 259, 37, 133, 41, 265, 545, 641, 769, 30, 70, 134, 74, 194, 322, 386, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_331, vertices_899, vertices_677, vertices_809, vertices_94, vertices_198, vertices_450, vertices_820, vertices_724, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_37, vertices_133, vertices_41, vertices_265, vertices_545, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_331), (false, vertices_899), (false, vertices_677), (false, vertices_809), (true, vertices_70), (true, vertices_194), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_88), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_720) then 20 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 135 70 194 84 532 196 88 304 336 784 448 331 899 677 809 720
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 724
cert_cover_5 4 0 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1513

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1514.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1514

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 689, 849, 142, 454, 202, 428, 184, 728, 992, 7, 27, 67, 37, 261, 49, 81, 529, 545, 321, 769, 14, 326, 134, 74, 138, 194, 44, 140, 292, 388, 56, 88, 152, 168, 200, 176, 592, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_689, vertices_849, vertices_142, vertices_454, vertices_202, vertices_428, vertices_184, vertices_728, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_769, vertices_14, vertices_326, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_292, vertices_388, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_689), (false, vertices_849), (true, vertices_134), (true, vertices_138), (true, vertices_194), (true, vertices_140), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 134 138 194 140 388 152 168 200 416 448 704 327 91 63 805 689 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 7 326
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 326 454 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 44 428 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 88 728 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1514

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1515.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1515

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 625, 961, 142, 454, 202, 428, 184, 728, 944, 7, 27, 67, 37, 261, 49, 81, 545, 321, 577, 769, 14, 326, 134, 74, 138, 194, 44, 140, 292, 388, 56, 88, 152, 168, 200, 176, 560, 592, 656, 416, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_625, vertices_961, vertices_142, vertices_454, vertices_202, vertices_428, vertices_184, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_326, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_292, vertices_388, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_560, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_625), (false, vertices_961), (true, vertices_134), (true, vertices_138), (true, vertices_194), (true, vertices_140), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 7 326
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 326 454 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 44 428 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 88 728 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1515

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1516.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1516

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 195, 421, 817, 721, 897, 334, 454, 812, 632, 968, 7, 27, 67, 131, 37, 133, 49, 81, 529, 289, 193, 385, 641, 769, 14, 326, 134, 74, 194, 44, 268, 292, 388, 56, 88, 552, 328, 584, 776, 560, 592, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_195, vertices_421, vertices_817, vertices_721, vertices_897, vertices_334, vertices_454, vertices_812, vertices_632, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_289, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_326, vertices_134, vertices_74, vertices_194, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_552, vertices_328, vertices_584, vertices_776, vertices_560, vertices_592, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_195), (false, vertices_421), (false, vertices_817), (false, vertices_721), (false, vertices_897), (true, vertices_326), (true, vertices_268), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_421) then 14 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (false, vertices_897) then 2 else
  if p.val = (true, vertices_326) then 11 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 7 326
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 326 454 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 632
cert_cover_5 3 2 2 3 4 5 56 632 3
cert_coverFacet 4 968
cert_cover_5 4 3 2 5 6 7 328 968 2
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1516

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1517.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1517

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 195, 677, 817, 721, 334, 454, 428, 312, 856, 992, 7, 27, 67, 131, 37, 133, 49, 81, 529, 545, 193, 641, 14, 326, 134, 74, 194, 44, 268, 164, 388, 56, 88, 280, 296, 328, 304, 592, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_195, vertices_677, vertices_817, vertices_721, vertices_334, vertices_454, vertices_428, vertices_312, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_326, vertices_134, vertices_74, vertices_194, vertices_44, vertices_268, vertices_164, vertices_388, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_304, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_195), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_326), (true, vertices_268), (true, vertices_388), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (true, vertices_326) then 12 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 7 326
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 326 454 3
cert_coverFacet 2 428
cert_cover_5 2 1 1 2 4 6 44 428 3
cert_coverFacet 3 312
cert_cover_2 3 3 2 4 7 56 312 3
cert_coverFacet 4 856
cert_cover_5 4 2 2 3 5 7 88 856 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1517

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1518.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1518

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 195, 677, 625, 961, 334, 454, 428, 312, 856, 944, 7, 27, 67, 131, 37, 133, 49, 81, 545, 193, 577, 641, 14, 326, 134, 74, 194, 44, 268, 164, 388, 56, 88, 280, 296, 328, 304, 560, 592, 784, 416, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_195, vertices_677, vertices_625, vertices_961, vertices_334, vertices_454, vertices_428, vertices_312, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_326, vertices_134, vertices_74, vertices_194, vertices_44, vertices_268, vertices_164, vertices_388, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_195), (false, vertices_677), (false, vertices_625), (false, vertices_961), (true, vertices_326), (true, vertices_268), (true, vertices_388), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_304), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_625) then 18 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_326) then 12 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 7 326
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 326 454 3
cert_coverFacet 2 428
cert_cover_5 2 1 1 2 4 6 44 428 3
cert_coverFacet 3 312
cert_cover_2 3 3 2 4 7 56 312 3
cert_coverFacet 4 856
cert_cover_5 4 2 2 3 5 7 88 856 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 304 944 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1518

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1519.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1519

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 195, 677, 625, 961, 334, 454, 428, 696, 856, 904, 7, 27, 67, 131, 37, 133, 49, 81, 545, 193, 577, 641, 14, 326, 134, 74, 194, 44, 268, 164, 388, 56, 88, 536, 168, 328, 392, 648, 776, 560, 592, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_195, vertices_677, vertices_625, vertices_961, vertices_334, vertices_454, vertices_428, vertices_696, vertices_856, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_326, vertices_134, vertices_74, vertices_194, vertices_44, vertices_268, vertices_164, vertices_388, vertices_56, vertices_88, vertices_536, vertices_168, vertices_328, vertices_392, vertices_648, vertices_776, vertices_560, vertices_592, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_195), (false, vertices_677), (false, vertices_625), (false, vertices_961), (true, vertices_326), (true, vertices_268), (true, vertices_388), (true, vertices_536), (true, vertices_168), (true, vertices_328), (true, vertices_392), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_625) then 18 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_326) then 12 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 7 326
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 326 454 3
cert_coverFacet 2 428
cert_cover_5 2 1 1 2 4 6 44 428 3
cert_coverFacet 3 696
cert_cover_5 3 2 2 3 4 6 56 696 3
cert_coverFacet 4 856
cert_cover_5 4 3 2 3 5 7 88 856 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1519

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1520.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1520

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 451, 805, 369, 897, 142, 202, 684, 824, 728, 976, 7, 27, 67, 131, 37, 517, 49, 81, 289, 321, 385, 641, 769, 14, 134, 74, 138, 194, 44, 140, 548, 644, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_451, vertices_805, vertices_369, vertices_897, vertices_142, vertices_202, vertices_684, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_548, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_451), (false, vertices_805), (false, vertices_369), (false, vertices_897), (true, vertices_138), (true, vertices_140), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_720), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_647) then 9 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_805) then 10 else
  if p.val = (false, vertices_369) then 17 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_720) then 18 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 1 5 2
cert_heightProof 3
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 728
cert_cover_5 4 0 2 3 5 6 88 728 3
cert_coverFacet 5 976
cert_cover_5 5 0 3 5 6 7 720 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1520

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1521.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1521

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 91, 451, 805, 369, 142, 902, 202, 684, 824, 728, 976, 7, 27, 67, 259, 37, 261, 49, 81, 289, 321, 14, 134, 262, 74, 138, 194, 386, 44, 140, 548, 644, 772, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_91, vertices_451, vertices_805, vertices_369, vertices_142, vertices_902, vertices_202, vertices_684, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_37, vertices_261, vertices_49, vertices_81, vertices_289, vertices_321, vertices_14, vertices_134, vertices_262, vertices_74, vertices_138, vertices_194, vertices_386, vertices_44, vertices_140, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_91), (false, vertices_451), (false, vertices_805), (false, vertices_369), (true, vertices_134), (true, vertices_138), (true, vertices_140), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_720), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_720) then 20 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
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
cert_row_2 0 3 5 6 8 720
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 134 902 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 728
cert_cover_5 5 0 2 3 5 6 88 728 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1521

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1522.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1522

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 195, 293, 901, 817, 721, 398, 458, 364, 632, 992, 7, 27, 67, 131, 37, 133, 261, 49, 81, 529, 289, 193, 641, 769, 14, 134, 74, 394, 194, 44, 268, 292, 388, 56, 88, 104, 328, 560, 592, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_195, vertices_293, vertices_901, vertices_817, vertices_721, vertices_398, vertices_458, vertices_364, vertices_632, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_261, vertices_49, vertices_81, vertices_529, vertices_289, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_394, vertices_194, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_104, vertices_328, vertices_560, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_195), (false, vertices_293), (false, vertices_901), (false, vertices_817), (false, vertices_721), (true, vertices_394), (true, vertices_268), (true, vertices_104), (true, vertices_328), (true, vertices_352), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 9 19 13 11 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_293) then 2 else
  if p.val = (false, vertices_901) then 10 else
  if p.val = (false, vertices_817) then 12 else
  if p.val = (false, vertices_721) then 16 else
  if p.val = (true, vertices_394) then 18 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 11 => Sum.inl 4
  | 12 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_4 1 1 2 4 5 7 364 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 364
cert_cover_5 2 1 1 2 4 5 44 364 3
cert_coverFacet 3 632
cert_cover_5 3 2 2 3 4 5 56 632 3
cert_coverFacet 4 992
cert_cover_5 4 3 4 5 6 7 352 992 2
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1522

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1523.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1523

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 195, 677, 817, 721, 398, 458, 812, 964, 376, 848, 7, 27, 67, 131, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 394, 194, 44, 268, 548, 388, 644, 772, 56, 88, 296, 328, 304, 336, 592, 784, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_195, vertices_677, vertices_817, vertices_721, vertices_398, vertices_458, vertices_812, vertices_964, vertices_376, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_394, vertices_194, vertices_44, vertices_268, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_336, vertices_592, vertices_784, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_195), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_394), (true, vertices_268), (true, vertices_388), (true, vertices_772), (true, vertices_296), (true, vertices_328), (true, vertices_336), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 10 20 14 12 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_677) then 11 else
  if p.val = (false, vertices_817) then 13 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (true, vertices_394) then 19 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 12 => Sum.inl 4
  | 13 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_4 1 1 5 6 7 8 964 388 1
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 964
cert_cover_5 3 1 1 5 6 7 388 964 1
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1523

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1524.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1524

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 142, 902, 202, 962, 428, 248, 464, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 134, 518, 74, 138, 194, 578, 898, 44, 140, 292, 388, 772, 56, 88, 168, 200, 176, 208, 336, 400, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_142, vertices_902, vertices_202, vertices_962, vertices_428, vertices_248, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_134, vertices_518, vertices_74, vertices_138, vertices_194, vertices_578, vertices_898, vertices_44, vertices_140, vertices_292, vertices_388, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_134), (true, vertices_138), (true, vertices_194), (true, vertices_898), (true, vertices_140), (true, vertices_388), (true, vertices_168), (true, vertices_200), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 9 12 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_805) then 11 else
  if p.val = (false, vertices_433) then 18 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_898) then 16 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 6 7 8 898
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_rows_3
cert_pivot_3 1 0 2
cert_heightProof 3
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 7 194 962 3
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 44 428 3
cert_coverFacet 5 248
cert_cover_5 5 2 2 3 4 5 56 248 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1524

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1525.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1525

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 195, 421, 817, 465, 590, 902, 962, 812, 632, 848, 7, 27, 67, 131, 37, 133, 49, 81, 273, 289, 193, 385, 14, 134, 518, 74, 194, 578, 898, 44, 524, 292, 388, 772, 56, 88, 552, 584, 560, 336, 592, 784, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_195, vertices_421, vertices_817, vertices_465, vertices_590, vertices_902, vertices_962, vertices_812, vertices_632, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_518, vertices_74, vertices_194, vertices_578, vertices_898, vertices_44, vertices_524, vertices_292, vertices_388, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_560, vertices_336, vertices_592, vertices_784, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_195), (false, vertices_421), (false, vertices_817), (false, vertices_465), (true, vertices_518), (true, vertices_578), (true, vertices_898), (true, vertices_524), (true, vertices_772), (true, vertices_552), (true, vertices_584), (true, vertices_592), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 10 12 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_421) then 11 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_898) then 16 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 6 7 8 898
cert_row_4 1 0 1 2 5 8 590 14 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 14 590 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1525

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1526.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1526

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 805, 369, 142, 202, 962, 684, 184, 472, 944, 7, 27, 67, 515, 37, 517, 49, 81, 289, 321, 769, 14, 134, 74, 138, 194, 834, 642, 44, 140, 548, 644, 56, 88, 152, 168, 200, 176, 304, 336, 400, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_805, vertices_369, vertices_142, vertices_202, vertices_962, vertices_684, vertices_184, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_834, vertices_642, vertices_44, vertices_140, vertices_548, vertices_644, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_369), (true, vertices_138), (true, vertices_194), (true, vertices_140), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 138 1 194 140 152 168 200 176 400 672 448 896 647 805 91 835 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1526

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1650 : Certifies 1650 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1496.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1651 : Certifies 1651 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1498.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1652 : Certifies 1652 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1499.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1653 : Certifies 1653 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1500.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1654 : Certifies 1654 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1501.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1655 : Certifies 1655 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1502.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1656 : Certifies 1656 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1503.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1657 : Certifies 1657 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1504.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1658 : Certifies 1658 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1505.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1659 : Certifies 1659 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1506.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1660 : Certifies 1660 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1507.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1661 : Certifies 1661 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1508.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1662 : Certifies 1662 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1509.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1663 : Certifies 1663 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1510.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1664 : Certifies 1664 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1511.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1665 : Certifies 1665 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1512.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1666 : Certifies 1666 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1513.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1667 : Certifies 1667 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1514.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1668 : Certifies 1668 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1515.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1669 : Certifies 1669 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1516.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1670 : Certifies 1670 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1517.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1671 : Certifies 1671 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1518.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1672 : Certifies 1672 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1519.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1673 : Certifies 1673 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1520.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1674 : Certifies 1674 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1521.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1675 : Certifies 1675 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1522.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1676 : Certifies 1676 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1523.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1677 : Certifies 1677 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1524.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1678 : Certifies 1678 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1525.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1679 : Certifies 1679 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1526.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B055 (j : Fin 30) :
    Certifies (1650 + j.val) := by
  fin_cases j
  · exact projection_1650
  · exact projection_1651
  · exact projection_1652
  · exact projection_1653
  · exact projection_1654
  · exact projection_1655
  · exact projection_1656
  · exact projection_1657
  · exact projection_1658
  · exact projection_1659
  · exact projection_1660
  · exact projection_1661
  · exact projection_1662
  · exact projection_1663
  · exact projection_1664
  · exact projection_1665
  · exact projection_1666
  · exact projection_1667
  · exact projection_1668
  · exact projection_1669
  · exact projection_1670
  · exact projection_1671
  · exact projection_1672
  · exact projection_1673
  · exact projection_1674
  · exact projection_1675
  · exact projection_1676
  · exact projection_1677
  · exact projection_1678
  · exact projection_1679

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
