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
/- Source: ProjectionCertificates/R_one_six_1628.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1628

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 142, 458, 812, 396, 900, 376, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 138, 194, 44, 140, 268, 548, 388, 644, 772, 56, 88, 296, 328, 392, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_142, vertices_458, vertices_812, vertices_396, vertices_900, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_268, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_138), (true, vertices_140), (true, vertices_268), (true, vertices_388), (true, vertices_772), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 140 268 388 772 296 328 392 336 448 896 199 91 63 677 817 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 396
cert_cover_2 3 2 1 6 7 140 396 3
cert_coverFacet 4 900
cert_cover_2 4 6 1 7 8 388 900 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1628

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1629.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1629

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 142, 458, 812, 652, 376, 904, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 138, 194, 44, 140, 524, 548, 644, 56, 88, 296, 328, 392, 648, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_142, vertices_458, vertices_812, vertices_652, vertices_376, vertices_904, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_138), (true, vertices_140), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 140 524 296 328 392 648 776 336 448 896 199 91 63 677 817 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1629

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1630.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1630

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 293, 901, 817, 721, 142, 458, 428, 632, 872, 960, 7, 27, 67, 37, 133, 261, 49, 81, 529, 289, 193, 641, 769, 14, 134, 74, 138, 194, 44, 140, 292, 388, 56, 88, 616, 296, 328, 392, 560, 592, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_293, vertices_901, vertices_817, vertices_721, vertices_142, vertices_458, vertices_428, vertices_632, vertices_872, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_261, vertices_49, vertices_81, vertices_529, vertices_289, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_292, vertices_388, vertices_56, vertices_88, vertices_616, vertices_296, vertices_328, vertices_392, vertices_560, vertices_592, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_293), (false, vertices_901), (false, vertices_817), (false, vertices_721), (true, vertices_138), (true, vertices_140), (true, vertices_616), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_901) then 13 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_616) then 15 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_832) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(true, vertices_616), by decide +kernel⟩
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
cert_row_2 0 2 4 5 8 616
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 1 2 4 6 7 428 44 3
cert_rows_3
cert_pivot_3 0 8 1
cert_heightProof 3
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 632
cert_cover_5 3 0 2 3 4 5 56 632 3
cert_coverFacet 4 872
cert_cover_5 4 0 2 4 5 7 616 872 3
cert_coverFacet 5 960
cert_cover_2 5 6 5 7 8 448 960 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1630

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1631.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1631

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 369, 481, 142, 458, 556, 908, 568, 856, 944, 7, 27, 67, 37, 133, 49, 81, 353, 161, 193, 14, 134, 74, 138, 194, 44, 140, 524, 548, 644, 56, 88, 536, 552, 328, 392, 776, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_369, vertices_481, vertices_142, vertices_458, vertices_556, vertices_908, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_353, vertices_161, vertices_193, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_392, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_369), (false, vertices_481), (true, vertices_138), (true, vertices_140), (true, vertices_524), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_392), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 19 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (false, vertices_481) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 6 7 8 908 140 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 140 908 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1631

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1632.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1632

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 142, 458, 556, 908, 376, 808, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 138, 194, 44, 140, 524, 548, 644, 56, 88, 296, 552, 328, 392, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_142, vertices_458, vertices_556, vertices_908, vertices_376, vertices_808, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_392, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_138), (true, vertices_140), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_392), (true, vertices_776), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 140 524 296 552 328 392 776 336 448 896 199 91 63 677 817 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 6 7 8 908 140 3
cert_row_2 2 3 5 6 8 720
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 1 6 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 140 908 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 976
cert_cover_5 6 2 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1632

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1633.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1633

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 142, 458, 300, 908, 804, 376, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 138, 194, 44, 140, 268, 292, 548, 644, 772, 56, 88, 296, 328, 392, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_142, vertices_458, vertices_300, vertices_908, vertices_804, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_268, vertices_292, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_138), (true, vertices_140), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 140 268 292 772 296 328 392 336 448 896 199 91 63 677 817 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 6 7 8 908 140 3
cert_row_2 2 3 5 6 8 720
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 1 6 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 140 908 3
cert_coverFacet 4 804
cert_cover_2 4 4 1 7 8 292 804 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 976
cert_cover_5 6 2 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1633

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1634.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1634

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 554, 372, 484, 568, 856, 904, 944, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 546, 642, 52, 84, 356, 164, 196, 56, 88, 536, 552, 328, 392, 648, 776, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_554, vertices_372, vertices_484, vertices_568, vertices_856, vertices_904, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_356), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_356) then 18 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 4 5 7 356
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 372
cert_cover_5 2 1 1 3 4 5 52 372 3
cert_coverFacet 3 484
cert_cover_5 3 1 1 4 5 6 356 484 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1634

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1635.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1635

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 554, 820, 724, 376, 808, 904, 976, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 546, 642, 52, 84, 532, 548, 196, 644, 56, 88, 296, 552, 328, 392, 648, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_554, vertices_820, vertices_724, vertices_376, vertices_808, vertices_904, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_720) then 21 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 820
cert_cover_5 2 2 1 3 4 7 52 820 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 976
cert_cover_5 7 1 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1635

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1636.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1636

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 422, 554, 930, 820, 468, 568, 856, 904, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 418, 546, 642, 52, 84, 276, 292, 196, 388, 56, 88, 536, 552, 328, 392, 648, 776, 560, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_422, vertices_554, vertices_930, vertices_820, vertices_468, vertices_568, vertices_856, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_418, vertices_546, vertices_642, vertices_52, vertices_84, vertices_276, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_392, vertices_648, vertices_776, vertices_560, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_418), (true, vertices_546), (true, vertices_276), (true, vertices_292), (true, vertices_388), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_93) then 14 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_418) then 18 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_418), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_2 0 0 4 6 7 418
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 38 422 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 930
cert_cover_5 2 0 0 4 6 8 418 930 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 84 468 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1636

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1637.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1637

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 451, 549, 369, 929, 206, 556, 652, 824, 728, 976, 7, 27, 67, 131, 37, 517, 49, 81, 289, 545, 321, 385, 641, 14, 134, 74, 194, 44, 140, 524, 548, 644, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_451, vertices_549, vertices_369, vertices_929, vertices_206, vertices_556, vertices_652, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_451), (false, vertices_549), (false, vertices_369), (false, vertices_929), (true, vertices_140), (true, vertices_524), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_720), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 8 14 15 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_647) then 9 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_369) then 16 else
  if p.val = (false, vertices_929) then 19 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_720) then 17 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 5 0 2
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 556
cert_cover_2 1 2 1 4 8 44 556 3
cert_coverFacet 2 652
cert_cover_2 2 2 1 6 8 140 652 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 728
cert_cover_5 4 1 2 3 5 6 88 728 3
cert_coverFacet 5 976
cert_cover_5 5 1 3 5 6 7 720 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1637

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1638.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1638

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 550, 646, 810, 692, 468, 376, 904, 944, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 518, 42, 522, 546, 642, 52, 84, 148, 548, 196, 644, 56, 88, 296, 328, 392, 648, 776, 688, 304, 336, 400, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_550, vertices_646, vertices_810, vertices_692, vertices_468, vertices_376, vertices_904, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_518, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_148, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_688, vertices_304, vertices_336, vertices_400, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_518), (true, vertices_546), (true, vertices_148), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_776), (true, vertices_688), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_688) then 21 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 3 4 6 8 688
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 550
cert_cover_2 0 1 0 4 8 38 550 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 7 42 810 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 84 468 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 7 688 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1638

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1639.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1639

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 550, 646, 810, 820, 724, 376, 904, 976, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 518, 42, 522, 546, 642, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 392, 648, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_550, vertices_646, vertices_810, vertices_820, vertices_724, vertices_376, vertices_904, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_518, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_518), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_720) then 21 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 550
cert_cover_2 0 1 0 4 8 38 550 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 42 810 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 724
cert_cover_5 4 0 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 976
cert_cover_5 7 0 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1639

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1640.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1640

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 810, 564, 468, 916, 376, 904, 816, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 546, 642, 52, 84, 404, 532, 548, 196, 644, 56, 88, 296, 328, 392, 648, 776, 304, 560, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_810, vertices_564, vertices_468, vertices_916, vertices_376, vertices_904, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_404, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_404), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 19 15 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_404) then 20 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 7 376 56 3
cert_row_2 1 1 3 6 7 404
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 0 2 4 7 8 810 42 3
cert_rows
cert_pivot_2 5 3 1 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 3 0 2 4 7 42 810 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 8 404 916 3
cert_coverFacet 5 376
cert_cover_5 5 0 2 3 4 5 56 376 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1640

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1641.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1641

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 810, 564, 852, 964, 376, 904, 816, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 546, 642, 52, 84, 532, 548, 196, 836, 644, 56, 88, 296, 328, 392, 648, 776, 304, 560, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_810, vertices_564, vertices_852, vertices_964, vertices_376, vertices_904, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_836, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_836), (true, vertices_644), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_836) then 18 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 5 7 8 836
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 7 84 852 3
cert_coverFacet 4 964
cert_cover_5 4 1 1 5 6 7 196 964 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1641

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1642.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1642

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 810, 564, 724, 376, 904, 816, 976, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 546, 642, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 392, 648, 776, 304, 560, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_810, vertices_564, vertices_724, vertices_376, vertices_904, vertices_816, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_720) then 21 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 976
cert_cover_5 7 1 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1642

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1643.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1643

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 810, 820, 852, 708, 376, 904, 960, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 546, 642, 52, 84, 788, 548, 196, 580, 644, 56, 88, 296, 328, 392, 648, 776, 304, 336, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_810, vertices_820, vertices_852, vertices_708, vertices_376, vertices_904, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_788, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_336, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_788), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_800), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 19 15 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_788) then 20 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_580) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 3 7 8 788
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 52 820 3
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 7 84 852 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1643

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1644.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1644

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 810, 564, 724, 376, 904, 880, 960, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 546, 642, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 392, 648, 776, 368, 560, 592, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_810, vertices_564, vertices_724, vertices_376, vertices_904, vertices_880, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_368, vertices_560, vertices_592, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_776), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_800), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_368) then 21 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 3 4 5 7 368
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 3 1 3 5 6 84 724 3
cert_coverFacet 4 376
cert_cover_5 4 1 2 3 4 5 56 376 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 880
cert_cover_5 6 1 3 4 5 8 368 880 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1644

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1645.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1645

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 810, 692, 468, 376, 904, 816, 912, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 546, 642, 52, 84, 148, 676, 196, 56, 88, 296, 328, 392, 648, 776, 304, 560, 336, 400, 656, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_810, vertices_692, vertices_468, vertices_376, vertices_904, vertices_816, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_148, vertices_676, vertices_196, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_400, vertices_656, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_148), (true, vertices_676), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_148) then 1 else
  if p.val = (true, vertices_676) then 18 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 1 4 6 8 676
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 692
cert_cover_5 2 1 1 3 4 6 52 692 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1645

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1646.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1646

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 421, 689, 721, 270, 390, 458, 812, 568, 856, 992, 7, 27, 67, 37, 133, 49, 81, 657, 161, 193, 14, 134, 262, 74, 266, 194, 386, 44, 268, 292, 388, 56, 88, 536, 552, 328, 776, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_421, vertices_689, vertices_721, vertices_270, vertices_390, vertices_458, vertices_812, vertices_568, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_657, vertices_161, vertices_193, vertices_14, vertices_134, vertices_262, vertices_74, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_421), (false, vertices_689), (false, vertices_721), (true, vertices_262), (true, vertices_266), (true, vertices_386), (true, vertices_268), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 262 266 386 268 536 552 328 776 800 448 832 199 91 63 421 689 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 458
cert_cover_5 2 0 0 2 5 6 74 458 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1646

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1647.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1647

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 270, 390, 458, 812, 900, 376, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 262, 74, 266, 194, 386, 44, 268, 548, 388, 644, 772, 56, 88, 296, 328, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_270, vertices_390, vertices_458, vertices_812, vertices_900, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_262, vertices_74, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_262), (true, vertices_266), (true, vertices_386), (true, vertices_268), (true, vertices_388), (true, vertices_772), (true, vertices_296), (true, vertices_328), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 262 266 386 268 388 772 296 328 336 448 896 199 91 63 677 817 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 458
cert_cover_5 2 0 0 2 5 6 74 458 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 900
cert_cover_2 4 6 1 7 8 388 900 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1647

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1648.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1648

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 177, 465, 782, 646, 458, 898, 812, 376, 944, 7, 27, 67, 37, 133, 49, 81, 145, 161, 193, 14, 134, 518, 74, 266, 194, 386, 642, 770, 44, 780, 548, 644, 56, 88, 296, 328, 176, 304, 336, 400, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_177, vertices_465, vertices_782, vertices_646, vertices_458, vertices_898, vertices_812, vertices_376, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_145, vertices_161, vertices_193, vertices_14, vertices_134, vertices_518, vertices_74, vertices_266, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_177), (false, vertices_465), (true, vertices_518), (true, vertices_266), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_780), (true, vertices_296), (true, vertices_328), (true, vertices_304), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_780) then 17 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 44 812 3
cert_coverFacet 5 376
cert_cover_5 5 2 2 3 4 5 56 376 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1648

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1649.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1649

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 550, 646, 810, 692, 468, 376, 944, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 518, 42, 266, 546, 642, 770, 52, 84, 148, 548, 196, 644, 56, 88, 296, 328, 688, 304, 336, 400, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_550, vertices_646, vertices_810, vertices_692, vertices_468, vertices_376, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_518, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_688, vertices_304, vertices_336, vertices_400, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_518), (true, vertices_546), (true, vertices_148), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_688), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_688) then 20 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 267 518 546 148 548 644 296 304 336 400 800 199 899 93 457 688
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 3 4 6 8 688
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 550
cert_cover_2 0 1 0 4 8 38 550 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 7 42 810 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 84 468 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 688 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1649

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1650.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1650

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 550, 646, 810, 820, 724, 376, 976, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 518, 42, 266, 546, 642, 770, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_550, vertices_646, vertices_810, vertices_820, vertices_724, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_518, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_518), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_720) then 20 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 267 518 546 532 548 644 296 304 336 784 800 199 899 93 457 720
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 550
cert_cover_2 0 1 0 4 8 38 550 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 42 810 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1650

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1651.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1651

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 810, 244, 568, 856, 688, 976, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 546, 642, 770, 52, 84, 164, 196, 56, 88, 536, 552, 328, 776, 176, 560, 208, 848, 656, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_810, vertices_244, vertices_568, vertices_856, vertices_688, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_208, vertices_848, vertices_656, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_848), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_848) then 20 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 267 546 164 536 552 776 176 560 208 656 672 199 899 93 457 848
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 3 5 7 8 848
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 3 1 3 4 5 52 244 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 856
cert_cover_5 4 1 2 3 5 7 88 856 3
cert_coverFacet 5 688
cert_cover_2 5 4 3 6 8 176 688 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1651

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1652.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1652

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 810, 244, 568, 856, 752, 960, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 546, 642, 770, 52, 84, 164, 196, 56, 88, 536, 552, 328, 776, 240, 560, 592, 672, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_810, vertices_244, vertices_568, vertices_856, vertices_752, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_240, vertices_560, vertices_592, vertices_672, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_240) then 20 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 267 546 164 536 552 776 560 592 672 704 832 199 899 93 457 240
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 1 1 3 4 5 52 244 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 856
cert_cover_5 4 3 2 3 5 7 88 856 3
cert_coverFacet 5 752
cert_cover_5 5 1 3 4 5 8 240 752 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1652

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1653.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1653

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 298, 802, 820, 724, 376, 976, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 290, 546, 642, 770, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_298, vertices_802, vertices_820, vertices_724, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_290), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_720) then 20 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 267 290 546 532 548 644 296 304 336 784 800 199 899 93 457 720
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1653

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1654.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1654

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 298, 802, 628, 964, 824, 856, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 290, 546, 642, 770, 52, 84, 548, 196, 580, 644, 56, 88, 792, 296, 328, 560, 592, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_298, vertices_802, vertices_628, vertices_964, vertices_824, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_792, vertices_296, vertices_328, vertices_560, vertices_592, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_290), (true, vertices_546), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_792), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_792) then 19 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 7 8 792
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 38 678 3
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 964
cert_cover_5 4 3 1 5 6 7 196 964 3
cert_coverFacet 5 824
cert_cover_5 5 0 2 3 4 7 56 824 3
cert_coverFacet 6 856
cert_cover_5 6 0 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1654

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1655.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1655

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 810, 564, 468, 916, 376, 816, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 546, 642, 770, 52, 84, 404, 532, 548, 196, 644, 56, 88, 296, 328, 304, 560, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_810, vertices_564, vertices_468, vertices_916, vertices_376, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_404, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_560, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_404), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 18 14 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_404) then 19 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 7 376 56 3
cert_row_2 1 1 3 6 7 404
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 0 2 4 7 8 810 42 3
cert_rows
cert_pivot_2 5 3 1 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 3 0 2 4 7 42 810 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 8 404 916 3
cert_coverFacet 5 376
cert_cover_5 5 0 2 3 4 5 56 376 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1655

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1656.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1656

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 810, 564, 852, 964, 376, 816, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 546, 642, 770, 52, 84, 532, 548, 196, 836, 644, 56, 88, 296, 328, 304, 560, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_810, vertices_564, vertices_852, vertices_964, vertices_376, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_836, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_560, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_836), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_836) then 17 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 5 7 8 836
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 7 84 852 3
cert_coverFacet 4 964
cert_cover_5 4 1 1 5 6 7 196 964 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1656

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1657.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1657

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 810, 564, 724, 376, 816, 976, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 546, 642, 770, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 304, 560, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_810, vertices_564, vertices_724, vertices_376, vertices_816, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_560, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_720) then 20 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 267 546 532 548 644 296 304 560 336 784 800 199 899 93 457 720
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1657

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1770 : Certifies 1770 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1628.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1771 : Certifies 1771 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1629.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1772 : Certifies 1772 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1630.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1773 : Certifies 1773 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1631.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1774 : Certifies 1774 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1632.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1775 : Certifies 1775 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1633.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1776 : Certifies 1776 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1634.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1777 : Certifies 1777 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1635.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1778 : Certifies 1778 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1636.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1779 : Certifies 1779 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1637.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1780 : Certifies 1780 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1638.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1781 : Certifies 1781 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1639.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1782 : Certifies 1782 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1640.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1783 : Certifies 1783 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1641.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1784 : Certifies 1784 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1642.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1785 : Certifies 1785 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1643.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1786 : Certifies 1786 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1644.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1787 : Certifies 1787 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1645.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1788 : Certifies 1788 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1646.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1789 : Certifies 1789 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1647.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1790 : Certifies 1790 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1648.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1791 : Certifies 1791 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1649.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1792 : Certifies 1792 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1650.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1793 : Certifies 1793 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1651.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1794 : Certifies 1794 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1652.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1795 : Certifies 1795 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1653.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1796 : Certifies 1796 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1654.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1797 : Certifies 1797 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1655.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1798 : Certifies 1798 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1656.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1799 : Certifies 1799 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1657.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B059 (j : Fin 30) :
    Certifies (1770 + j.val) := by
  fin_cases j
  · exact projection_1770
  · exact projection_1771
  · exact projection_1772
  · exact projection_1773
  · exact projection_1774
  · exact projection_1775
  · exact projection_1776
  · exact projection_1777
  · exact projection_1778
  · exact projection_1779
  · exact projection_1780
  · exact projection_1781
  · exact projection_1782
  · exact projection_1783
  · exact projection_1784
  · exact projection_1785
  · exact projection_1786
  · exact projection_1787
  · exact projection_1788
  · exact projection_1789
  · exact projection_1790
  · exact projection_1791
  · exact projection_1792
  · exact projection_1793
  · exact projection_1794
  · exact projection_1795
  · exact projection_1796
  · exact projection_1797
  · exact projection_1798
  · exact projection_1799

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
