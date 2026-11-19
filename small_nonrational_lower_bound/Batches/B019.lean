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
/- Source: ProjectionCertificates/R_multi_six_0048.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0048

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 149, 809, 753, 782, 838, 412, 452, 440, 992, 7, 11, 67, 21, 133, 41, 521, 49, 145, 545, 193, 577, 14, 70, 774, 522, 578, 28, 268, 148, 196, 324, 388, 56, 408, 296, 776, 176, 736, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_809, vertices_753, vertices_782, vertices_838, vertices_412, vertices_452, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_193, vertices_577, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_196, vertices_324, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_736, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_809), (false, vertices_753), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_408), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 9 7 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_809) then 12 else
  if p.val = (false, vertices_753) then 18 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_408) then 8 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_832) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 7 => Sum.inl 3
  | 8 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_753), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 6 8 736
cert_row_2 1 2 3 6 7 408
cert_row_2 2 0 1 7 8 774
cert_rows_3
cert_pivot_3 2 4 0
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 2 0 1 5 7 70 838 3
cert_coverFacet 2 412
cert_cover_5 2 1 1 2 3 6 28 412 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 7 736 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0048

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_multi_six_0049.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0049

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 858, 172, 628, 740, 440, 944, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 330, 82, 44, 140, 52, 84, 612, 164, 196, 56, 280, 168, 392, 432, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_858, vertices_172, vertices_628, vertices_740, vertices_440, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_330, vertices_82, vertices_44, vertices_140, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_280, vertices_168, vertices_392, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_612) then 15 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_672) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
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
cert_row_2 0 1 4 5 8 612
cert_row_2 1 3 4 6 7 432
cert_row_4 2 0 2 3 5 7 858 26 3
cert_row_4 3 0 2 3 5 8 858 26 3
cert_rows
cert_pivot_2 1 4 7 0
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 858
cert_cover_2 1 2 0 3 5 26 858 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 52 628 3
cert_coverFacet 4 740
cert_cover_5 4 0 1 4 5 6 612 740 3
cert_coverFacet 5 440
cert_cover_5 5 1 2 3 4 6 56 440 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0049

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_multi_six_0050.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0050

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 341, 233, 369, 782, 838, 706, 284, 952, 992, 7, 11, 131, 21, 69, 41, 137, 49, 337, 97, 193, 14, 70, 774, 522, 194, 578, 642, 28, 268, 276, 324, 56, 280, 168, 648, 776, 304, 224, 352, 928, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_341, vertices_233, vertices_369, vertices_782, vertices_838, vertices_706, vertices_284, vertices_952, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_337, vertices_97, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_276, vertices_324, vertices_56, vertices_280, vertices_168, vertices_648, vertices_776, vertices_304, vertices_224, vertices_352, vertices_928, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_341), (false, vertices_233), (false, vertices_369), (true, vertices_774), (true, vertices_578), (true, vertices_268), (true, vertices_280), (true, vertices_776), (true, vertices_928), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 6 9 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_651) then 7 else
  if p.val = (false, vertices_341) then 11 else
  if p.val = (false, vertices_233) then 8 else
  if p.val = (false, vertices_369) then 12 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_928) then 18 else
  if p.val = (true, vertices_704) then 4 else
  if p.val = (true, vertices_832) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 6 => Sum.inl 2
  | 7 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 9 => Sum.inl 3
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(true, vertices_928), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 6 7 952 56 3
cert_row_4 2 2 3 4 6 8 952 56 3
cert_rows_3
cert_pivot_3 7 0 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 952
cert_cover_2 4 3 2 4 6 56 952 3
cert_coverFacet 5 992
cert_cover 5 6 3 4 5 3 2 7 4 224 992 928 56 952 6
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0050

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_multi_six_0054.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0054

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 331, 781, 961, 214, 250, 300, 820, 660, 708, 488, 944, 7, 11, 67, 13, 517, 265, 321, 577, 769, 22, 70, 58, 74, 210, 44, 268, 52, 148, 532, 292, 196, 580, 644, 772, 232, 296, 328, 176, 816, 656, 416, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_331, vertices_781, vertices_961, vertices_214, vertices_250, vertices_300, vertices_820, vertices_660, vertices_708, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_265, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_58, vertices_74, vertices_210, vertices_44, vertices_268, vertices_52, vertices_148, vertices_532, vertices_292, vertices_196, vertices_580, vertices_644, vertices_772, vertices_232, vertices_296, vertices_328, vertices_176, vertices_816, vertices_656, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_331), (false, vertices_781), (false, vertices_961), (true, vertices_210), (true, vertices_148), (true, vertices_532), (true, vertices_292), (true, vertices_196), (true, vertices_644), (true, vertices_232), (true, vertices_296), (true, vertices_176), (true, vertices_816), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 9 16 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_781) then 11 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_148) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_232) then 17 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_816) then 19 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 2 3 5 4 250 58 3
cert_row_4 2 0 2 3 5 6 250 58 3
cert_rows_3
cert_pivot_3 4 7 0
cert_heightProof 3
cert_coverFacet 0 214
cert_cover 0 3 2 0 1 3 0 5 3 22 214 210 58 250 5
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 488
cert_cover 6 5 2 2 4 3 0 7 3 232 488 232 58 250 5
cert_coverFacet 7 944
cert_cover_5 7 0 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0054

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_multi_six_0055.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0055

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 331, 781, 961, 214, 250, 812, 564, 660, 708, 488, 944, 7, 11, 67, 13, 517, 265, 321, 577, 769, 22, 70, 58, 74, 210, 44, 780, 52, 148, 532, 548, 196, 580, 644, 232, 296, 328, 176, 560, 656, 416, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_331, vertices_781, vertices_961, vertices_214, vertices_250, vertices_812, vertices_564, vertices_660, vertices_708, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_265, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_58, vertices_74, vertices_210, vertices_44, vertices_780, vertices_52, vertices_148, vertices_532, vertices_548, vertices_196, vertices_580, vertices_644, vertices_232, vertices_296, vertices_328, vertices_176, vertices_560, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_331), (false, vertices_781), (false, vertices_961), (true, vertices_210), (true, vertices_148), (true, vertices_532), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_232), (true, vertices_296), (true, vertices_176), (true, vertices_560), (true, vertices_656), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_781) then 13 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_210) then 17 else
  if p.val = (true, vertices_148) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_232) then 19 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 3 4 6 7 8 944 176 3
cert_row_4 2 0 2 3 5 4 250 58 3
cert_row_4 3 0 2 3 5 6 250 58 3
cert_rows
cert_pivot_2 1 7 4 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover 0 3 2 0 1 3 0 5 3 22 214 210 58 250 5
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 488
cert_cover 6 5 2 2 4 3 0 7 3 232 488 232 58 250 5
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0055

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_multi_six_0056.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0056

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 331, 771, 589, 961, 790, 250, 466, 556, 436, 932, 744, 7, 11, 259, 515, 13, 517, 73, 321, 577, 769, 22, 518, 58, 74, 210, 274, 322, 770, 44, 524, 52, 276, 420, 548, 772, 232, 552, 584, 176, 400, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_331, vertices_771, vertices_589, vertices_961, vertices_790, vertices_250, vertices_466, vertices_556, vertices_436, vertices_932, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_518, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_420, vertices_548, vertices_772, vertices_232, vertices_552, vertices_584, vertices_176, vertices_400, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_331), (false, vertices_771), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_276), (true, vertices_420), (true, vertices_548), (true, vertices_772), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_210) then 12 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_420) then 16 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_232) then 18 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 8 790 22 3
cert_row_2 1 1 4 6 7 420
cert_row_4 2 0 2 3 5 4 250 58 3
cert_row_4 3 0 2 3 5 6 250 58 3
cert_rows
cert_pivot_2 8 1 4 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 466
cert_cover 2 5 2 0 3 3 0 7 3 210 466 210 58 250 5
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 436
cert_cover_5 4 1 1 3 4 6 52 436 3
cert_coverFacet 5 932
cert_cover_5 5 1 1 4 6 8 420 932 3
cert_coverFacet 6 744
cert_cover 6 5 2 2 4 3 0 8 3 232 744 232 58 250 5
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0056

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_multi_six_0057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 653, 961, 790, 250, 850, 812, 308, 424, 904, 496, 7, 11, 67, 13, 517, 137, 193, 577, 641, 22, 518, 58, 202, 82, 786, 578, 44, 524, 52, 276, 292, 772, 168, 296, 392, 648, 776, 240, 304, 336, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_790, vertices_250, vertices_850, vertices_812, vertices_308, vertices_424, vertices_904, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_786, vertices_578, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 17 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_240) then 20 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 6 250 58 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_2 2 0 3 7 8 786
cert_row_4 3 0 2 3 5 4 250 58 3
cert_rows
cert_pivot_2 6 1 7 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 22 790 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 496
cert_cover 7 5 2 3 4 3 0 7 3 240 496 240 58 250 5
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0057

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_multi_six_0058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 653, 961, 790, 250, 850, 812, 308, 680, 496, 928, 7, 11, 67, 13, 517, 137, 193, 577, 641, 22, 518, 58, 202, 82, 786, 578, 44, 524, 52, 276, 292, 772, 168, 552, 648, 240, 304, 336, 416, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_790, vertices_250, vertices_850, vertices_812, vertices_308, vertices_680, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_786, vertices_578, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_552), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 17 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_240) then 20 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 6 250 58 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_2 2 0 3 7 8 786
cert_row_4 3 0 2 3 5 4 250 58 3
cert_rows
cert_pivot_2 6 1 7 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 22 790 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 496
cert_cover 6 5 2 3 4 3 0 7 3 240 496 240 58 250 5
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0058

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_multi_six_0059.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0059

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 789, 249, 849, 654, 962, 556, 308, 804, 936, 496, 7, 11, 67, 21, 517, 57, 201, 81, 785, 577, 14, 518, 138, 194, 578, 642, 44, 524, 52, 276, 292, 548, 772, 168, 552, 648, 240, 304, 336, 416, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_789, vertices_249, vertices_849, vertices_654, vertices_962, vertices_556, vertices_308, vertices_804, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_517, vertices_57, vertices_201, vertices_81, vertices_785, vertices_577, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_772, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_789), (false, vertices_249), (false, vertices_849), (true, vertices_642), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 14 17 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 194 962 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 804
cert_cover_2 4 4 1 7 8 292 804 3
cert_coverFacet 5 936
cert_cover_5 5 3 2 4 6 7 168 936 3
cert_coverFacet 6 496
cert_cover_5 6 0 3 4 5 7 240 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0059

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_multi_six_0060.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0060

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 789, 249, 849, 654, 962, 300, 780, 308, 936, 496, 7, 11, 67, 21, 517, 57, 201, 81, 785, 577, 14, 518, 138, 194, 578, 642, 44, 268, 524, 52, 276, 292, 772, 168, 296, 648, 776, 240, 304, 336, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_789, vertices_249, vertices_849, vertices_654, vertices_962, vertices_300, vertices_780, vertices_308, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_517, vertices_57, vertices_201, vertices_81, vertices_785, vertices_577, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_168, vertices_296, vertices_648, vertices_776, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_789), (false, vertices_249), (false, vertices_849), (true, vertices_642), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_296), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 14 17 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 194 962 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 936
cert_cover_5 5 3 2 4 6 7 168 936 3
cert_coverFacet 6 496
cert_cover_5 6 0 3 4 5 7 240 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0060

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_multi_six_0061.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0061

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 835, 341, 249, 654, 706, 556, 820, 936, 496, 960, 7, 11, 67, 771, 21, 261, 57, 201, 81, 321, 14, 518, 138, 194, 578, 642, 44, 524, 52, 276, 548, 772, 168, 552, 648, 240, 304, 336, 416, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_835, vertices_341, vertices_249, vertices_654, vertices_706, vertices_556, vertices_820, vertices_936, vertices_496, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_261, vertices_57, vertices_201, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_835), (false, vertices_341), (false, vertices_249), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 11 13 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_249) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_59 1 642 2 524 0 548 552 648 304 416 800 448 704 896 341 63 203 775 835 249
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 936
cert_cover_5 4 3 2 4 6 7 168 936 3
cert_coverFacet 5 496
cert_cover_5 5 0 3 4 5 7 240 496 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0061

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_multi_six_0062.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0062

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 651, 341, 837, 553, 817, 206, 582, 962, 252, 936, 496, 7, 11, 515, 21, 325, 517, 41, 521, 49, 273, 545, 769, 14, 70, 518, 138, 194, 578, 642, 60, 204, 84, 580, 168, 552, 648, 240, 304, 336, 416, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_651, vertices_341, vertices_837, vertices_553, vertices_817, vertices_206, vertices_582, vertices_962, vertices_252, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_325, vertices_517, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_60, vertices_204, vertices_84, vertices_580, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_651), (false, vertices_341), (false, vertices_837), (false, vertices_553), (false, vertices_817), (true, vertices_70), (true, vertices_194), (true, vertices_578), (true, vertices_204), (true, vertices_168), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 14 11 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 2 4 6 7 8 936 168 3
cert_row_4 2 1 2 3 5 4 252 60 3
cert_row_4 3 1 2 3 5 6 252 60 3
cert_rows
cert_pivot_2 0 7 4 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover 0 2 2 0 1 3 1 5 3 14 206 204 60 252 5
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 252
cert_cover_2 3 2 1 3 5 60 252 3
cert_coverFacet 4 936
cert_cover_5 4 1 2 4 6 7 168 936 3
cert_coverFacet 5 496
cert_cover 5 5 2 3 4 3 1 7 3 240 496 240 60 252 5
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0062

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_multi_six_0063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 651, 277, 837, 553, 817, 206, 962, 252, 340, 936, 496, 7, 11, 515, 21, 581, 261, 41, 521, 49, 273, 545, 769, 14, 70, 138, 194, 578, 642, 60, 204, 84, 276, 324, 168, 552, 648, 240, 304, 336, 416, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_651, vertices_277, vertices_837, vertices_553, vertices_817, vertices_206, vertices_962, vertices_252, vertices_340, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_581, vertices_261, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_578, vertices_642, vertices_60, vertices_204, vertices_84, vertices_276, vertices_324, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_651), (false, vertices_277), (false, vertices_837), (false, vertices_553), (false, vertices_817), (true, vertices_194), (true, vertices_204), (true, vertices_84), (true, vertices_168), (true, vertices_240), (true, vertices_336), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 14 11 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 2 4 6 7 8 936 168 3
cert_row_4 2 1 2 3 5 4 252 60 3
cert_row_4 3 1 2 3 5 6 252 60 3
cert_rows
cert_pivot_2 0 7 4 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover 0 2 2 0 1 3 1 5 3 14 206 204 60 252 5
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 252
cert_cover_2 2 2 1 3 5 60 252 3
cert_coverFacet 3 340
cert_cover_2 3 3 1 5 7 84 340 3
cert_coverFacet 4 936
cert_cover_5 4 1 2 4 6 7 168 936 3
cert_coverFacet 5 496
cert_cover 5 5 2 3 4 3 1 7 3 240 496 240 60 252 5
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0063

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_multi_six_0064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 651, 341, 773, 553, 817, 206, 838, 962, 252, 936, 496, 7, 11, 515, 21, 261, 517, 41, 521, 49, 273, 545, 769, 14, 70, 518, 138, 194, 834, 642, 60, 204, 84, 324, 772, 168, 552, 648, 240, 304, 336, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_651, vertices_341, vertices_773, vertices_553, vertices_817, vertices_206, vertices_838, vertices_962, vertices_252, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_261, vertices_517, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_834, vertices_642, vertices_60, vertices_204, vertices_84, vertices_324, vertices_772, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_651), (false, vertices_341), (false, vertices_773), (false, vertices_553), (false, vertices_817), (true, vertices_70), (true, vertices_194), (true, vertices_834), (true, vertices_204), (true, vertices_168), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_553) then 2 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_834) then 11 else
  if p.val = (true, vertices_204) then 15 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_4 1 2 4 6 7 8 936 168 3
cert_row_4 2 1 2 3 5 4 252 60 3
cert_row_4 3 1 2 3 5 6 252 60 3
cert_rows
cert_pivot_2 0 7 4 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover 0 2 2 0 1 3 1 5 3 14 206 204 60 252 5
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 252
cert_cover_2 3 2 1 3 5 60 252 3
cert_coverFacet 4 936
cert_cover_5 4 1 2 4 6 7 168 936 3
cert_coverFacet 5 496
cert_cover 5 5 2 3 4 3 1 7 3 240 496 240 60 252 5
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0064

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_multi_six_0065.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0065

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 653, 961, 534, 250, 850, 812, 820, 424, 904, 496, 7, 11, 67, 13, 517, 137, 193, 577, 641, 22, 518, 58, 202, 82, 530, 578, 44, 524, 52, 532, 804, 168, 296, 392, 648, 776, 240, 304, 336, 784, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_534, vertices_250, vertices_850, vertices_812, vertices_820, vertices_424, vertices_904, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_530, vertices_578, vertices_44, vertices_524, vertices_52, vertices_532, vertices_804, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_240, vertices_304, vertices_336, vertices_784, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_530), (true, vertices_532), (true, vertices_804), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_804) then 17 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_240) then 20 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 2 3 5 4 250 58 3
cert_row_4 2 0 2 3 5 6 250 58 3
cert_row_4 3 0 3 5 7 8 850 82 3
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 850
cert_cover_5 2 3 0 3 5 7 82 850 3
cert_coverFacet 3 812
cert_cover_5 3 0 1 2 4 7 44 812 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 496
cert_cover 7 5 2 3 4 3 0 7 3 240 496 240 58 250 5
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0065

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_multi_six_0066.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0066

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 779, 597, 425, 817, 270, 326, 962, 252, 460, 752, 928, 7, 11, 515, 21, 581, 41, 265, 49, 529, 289, 769, 14, 70, 262, 266, 322, 578, 770, 60, 204, 268, 84, 324, 168, 392, 240, 560, 592, 416, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_779, vertices_597, vertices_425, vertices_817, vertices_270, vertices_326, vertices_962, vertices_252, vertices_460, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_581, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_578, vertices_770, vertices_60, vertices_204, vertices_268, vertices_84, vertices_324, vertices_168, vertices_392, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_779), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_262), (true, vertices_322), (true, vertices_204), (true, vertices_268), (true, vertices_324), (true, vertices_240), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 14 10 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_779) then 9 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_425) then 12 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_672) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 322 2
cert_row_4 1 1 2 3 5 4 252 60 3
cert_row_4 2 1 2 3 5 6 252 60 3
cert_rows_3
cert_pivot_3 4 0 1
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 322 962 2
cert_coverFacet 3 252
cert_cover_2 3 2 1 3 5 60 252 3
cert_coverFacet 4 460
cert_cover 4 5 2 1 2 3 1 7 3 204 460 204 60 252 5
cert_coverFacet 5 752
cert_cover 5 5 2 3 4 3 1 8 3 240 752 240 60 252 5
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0066

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_multi_six_0068.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0068

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 278, 122, 850, 940, 820, 744, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 396, 52, 276, 804, 104, 680, 200, 112, 560, 592, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_850, vertices_940, vertices_820, vertices_744, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_396, vertices_52, vertices_276, vertices_804, vertices_104, vertices_680, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_276), (true, vertices_804), (true, vertices_104), (true, vertices_680), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_804) then 15 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_680) then 17 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
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
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_2 1 0 2 3 4 58
cert_row_4 2 1 2 4 6 7 940 44 3
cert_row_4 3 1 2 4 6 8 940 44 3
cert_rows
cert_pivot_2 5 0 7 2
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 940
cert_cover_2 3 2 1 4 6 44 940 3
cert_coverFacet 4 820
cert_cover 4 4 2 1 3 3 1 7 4 52 820 804 44 940 6
cert_coverFacet 5 744
cert_cover 5 5 2 2 4 3 1 6 4 104 744 680 44 940 6
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0068

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_multi_six_0070.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0070

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 589, 961, 278, 250, 466, 556, 692, 916, 744, 7, 11, 259, 13, 517, 73, 321, 577, 769, 22, 262, 58, 74, 210, 274, 322, 44, 524, 52, 660, 276, 548, 772, 232, 552, 584, 176, 400, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_589, vertices_961, vertices_278, vertices_250, vertices_466, vertices_556, vertices_692, vertices_916, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_44, vertices_524, vertices_52, vertices_660, vertices_276, vertices_548, vertices_772, vertices_232, vertices_552, vertices_584, vertices_176, vertices_400, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_660), (true, vertices_276), (true, vertices_548), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 9 18 7 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_589) then 12 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_660) then 17 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_232) then 8 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_672) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inl 4
  | 8 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 6 8 660
cert_row_4 1 0 2 3 5 4 250 58 3
cert_row_4 2 0 2 3 5 6 250 58 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 466
cert_cover 2 5 2 0 3 3 0 7 3 210 466 210 58 250 5
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 692
cert_cover_5 4 0 1 3 4 6 52 692 3
cert_coverFacet 5 916
cert_cover_5 5 0 1 3 6 7 660 916 3
cert_coverFacet 6 744
cert_cover 6 5 2 2 4 3 0 8 3 232 744 232 58 250 5
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0070

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_multi_six_0071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 589, 961, 278, 250, 466, 556, 436, 932, 744, 7, 11, 259, 13, 517, 73, 321, 577, 769, 22, 262, 58, 74, 210, 274, 322, 44, 524, 52, 276, 420, 548, 772, 232, 552, 584, 176, 400, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_589, vertices_961, vertices_278, vertices_250, vertices_466, vertices_556, vertices_436, vertices_932, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_44, vertices_524, vertices_52, vertices_276, vertices_420, vertices_548, vertices_772, vertices_232, vertices_552, vertices_584, vertices_176, vertices_400, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_276), (true, vertices_420), (true, vertices_548), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 16 7 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_210) then 8 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_420) then 15 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_232) then 17 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_672) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inl 3
  | 8 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 6 7 420
cert_row_4 1 0 2 3 5 4 250 58 3
cert_row_4 2 0 2 3 5 6 250 58 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 466
cert_cover 2 5 2 0 3 3 0 7 3 210 466 210 58 250 5
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 436
cert_cover_5 4 0 1 3 4 6 52 436 3
cert_coverFacet 5 932
cert_cover_5 5 0 1 4 6 8 420 932 3
cert_coverFacet 6 744
cert_cover 6 5 2 2 4 3 0 8 3 232 744 232 58 250 5
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0071

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_multi_six_0072.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0072

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 589, 961, 278, 250, 466, 556, 820, 744, 944, 7, 11, 259, 13, 517, 73, 321, 577, 769, 22, 262, 58, 74, 210, 274, 322, 44, 524, 52, 276, 548, 772, 232, 552, 584, 176, 816, 400, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_589, vertices_961, vertices_278, vertices_250, vertices_466, vertices_556, vertices_820, vertices_744, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_232, vertices_552, vertices_584, vertices_176, vertices_816, vertices_400, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_276), (true, vertices_548), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_816), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 7 14 16 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_775) then 8 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_589) then 9 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_210) then 13 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_232) then 15 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_672) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inl 1
  | 8 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 2 3 5 4 250 58 3
cert_row_4 2 0 2 3 5 6 250 58 3
cert_rows_3
cert_pivot_3 4 7 0
cert_heightProof 3
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 466
cert_cover 2 5 2 0 3 3 0 7 3 210 466 210 58 250 5
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 744
cert_cover 5 5 2 2 4 3 0 8 3 232 744 232 58 250 5
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0072

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_multi_six_0073.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0073

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 589, 961, 790, 250, 466, 556, 692, 744, 912, 7, 11, 259, 13, 517, 73, 321, 577, 769, 22, 774, 58, 74, 210, 274, 322, 44, 524, 52, 532, 548, 232, 552, 584, 176, 400, 656, 784, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_589, vertices_961, vertices_790, vertices_250, vertices_466, vertices_556, vertices_692, vertices_744, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_774, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_232, vertices_552, vertices_584, vertices_176, vertices_400, vertices_656, vertices_784, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_532), (true, vertices_548), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 9 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_589) then 11 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_232) then 17 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_672) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
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
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 0 2 3 5 4 250 58 3
cert_row_4 3 0 2 3 5 6 250 58 3
cert_rows
cert_pivot_2 7 1 4 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 466
cert_cover 2 5 2 0 3 3 0 7 3 210 466 210 58 250 5
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 744
cert_cover 5 5 2 2 4 3 0 8 3 232 744 232 58 250 5
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0073

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_multi_six_0074.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 589, 961, 790, 250, 466, 556, 564, 744, 944, 7, 11, 259, 13, 517, 73, 321, 577, 769, 22, 774, 58, 74, 210, 274, 322, 44, 524, 52, 532, 548, 232, 552, 584, 176, 560, 400, 784, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_589, vertices_961, vertices_790, vertices_250, vertices_466, vertices_556, vertices_564, vertices_744, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_774, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_232, vertices_552, vertices_584, vertices_176, vertices_560, vertices_400, vertices_784, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_532), (true, vertices_548), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_400), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 9 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_589) then 11 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_232) then 17 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_672) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
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
cert_row_2 0 0 1 7 8 774
cert_row_4 1 3 4 6 7 8 944 176 3
cert_row_4 2 0 2 3 5 4 250 58 3
cert_row_4 3 0 2 3 5 6 250 58 3
cert_rows
cert_pivot_2 1 7 4 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 466
cert_cover 2 5 2 0 3 3 0 7 3 210 466 210 58 250 5
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 744
cert_cover 5 5 2 2 4 3 0 8 3 232 744 232 58 250 5
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0074

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_multi_six_0075.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 781, 393, 961, 790, 250, 850, 428, 308, 496, 7, 11, 67, 13, 517, 137, 265, 193, 577, 385, 769, 22, 518, 58, 202, 82, 786, 578, 44, 268, 52, 276, 292, 772, 168, 392, 240, 304, 336, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_781, vertices_393, vertices_961, vertices_790, vertices_250, vertices_850, vertices_428, vertices_308, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_265, vertices_193, vertices_577, vertices_385, vertices_769, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_786, vertices_578, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_772, vertices_168, vertices_392, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_781), (false, vertices_393), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_276), (true, vertices_292), (true, vertices_168), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 15 16 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_583) then 9 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_781) then 10 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_786) then 14 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_416) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 7 8 786
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 0 2 3 5 4 250 58 3
cert_row_4 3 0 2 3 5 6 250 58 3
cert_rows
cert_pivot_2 8 1 4 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 44 428 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 496
cert_cover 5 5 2 3 4 3 0 7 3 240 496 240 58 250 5
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0075

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_multi_six_0076.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 653, 961, 790, 250, 850, 428, 308, 900, 496, 7, 11, 67, 13, 517, 137, 193, 577, 641, 22, 518, 58, 202, 82, 786, 578, 44, 140, 52, 276, 292, 388, 644, 772, 168, 240, 304, 336, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_790, vertices_250, vertices_850, vertices_428, vertices_308, vertices_900, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_786, vertices_578, vertices_44, vertices_140, vertices_52, vertices_276, vertices_292, vertices_388, vertices_644, vertices_772, vertices_168, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_276), (true, vertices_292), (true, vertices_388), (true, vertices_772), (true, vertices_168), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 9 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_653) then 11 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 15 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 7 8 786
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 0 2 3 5 4 250 58 3
cert_row_4 3 0 2 3 5 6 250 58 3
cert_rows
cert_pivot_2 8 1 4 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 44 428 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 496
cert_cover 6 5 2 3 4 3 0 7 3 240 496 240 58 250 5
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0076

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_multi_six_0077.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0077

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 653, 961, 790, 250, 850, 172, 308, 932, 496, 7, 11, 67, 13, 517, 137, 193, 577, 641, 22, 518, 58, 202, 82, 786, 578, 44, 140, 52, 276, 164, 292, 644, 772, 168, 240, 304, 336, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_790, vertices_250, vertices_850, vertices_172, vertices_308, vertices_932, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_786, vertices_578, vertices_44, vertices_140, vertices_52, vertices_276, vertices_164, vertices_292, vertices_644, vertices_772, vertices_168, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 9 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_653) then 11 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 15 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 6 7 8 932 164 3
cert_row_2 1 0 3 7 8 786
cert_row_4 2 0 2 3 5 4 250 58 3
cert_row_4 3 0 2 3 5 6 250 58 3
cert_rows
cert_pivot_2 1 7 4 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 22 790 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 932
cert_cover_5 5 0 1 4 6 7 164 932 3
cert_coverFacet 6 496
cert_cover 6 5 2 3 4 3 0 7 3 240 496 240 58 250 5
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0077

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_multi_six_0078.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0078

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 533, 249, 849, 654, 962, 684, 820, 496, 928, 7, 11, 67, 21, 517, 57, 201, 81, 529, 577, 14, 518, 138, 194, 578, 642, 44, 652, 52, 532, 548, 168, 240, 304, 336, 784, 416, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_533, vertices_249, vertices_849, vertices_654, vertices_962, vertices_684, vertices_820, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_517, vertices_57, vertices_201, vertices_81, vertices_529, vertices_577, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_652, vertices_52, vertices_532, vertices_548, vertices_168, vertices_240, vertices_304, vertices_336, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_533), (false, vertices_249), (false, vertices_849), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 13 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_249) then 17 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_652) then 12 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_304) then 3 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 3 4 5 6 240
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 0 5 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 496
cert_cover_5 4 2 3 4 5 7 240 496 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0078

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_multi_six_0079.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0079

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 341, 249, 654, 962, 684, 820, 836, 496, 928, 7, 11, 67, 21, 69, 57, 201, 81, 14, 518, 138, 194, 578, 642, 44, 652, 52, 276, 548, 324, 580, 772, 168, 240, 304, 336, 416, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_341, vertices_249, vertices_654, vertices_962, vertices_684, vertices_820, vertices_836, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_57, vertices_201, vertices_81, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_324, vertices_580, vertices_772, vertices_168, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_341), (false, vertices_249), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_772), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_583) then 11 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_652) then 14 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_304) then 3 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 3 4 5 6 240
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 0 5 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 496
cert_cover_5 5 2 3 4 5 7 240 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0079

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_multi_six_0080.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0080

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 323, 341, 249, 654, 962, 684, 820, 496, 928, 7, 11, 67, 259, 21, 261, 57, 201, 81, 321, 14, 518, 138, 194, 322, 642, 770, 44, 652, 52, 276, 548, 772, 168, 240, 304, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_341, vertices_249, vertices_654, vertices_962, vertices_684, vertices_820, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_261, vertices_57, vertices_201, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_341), (false, vertices_249), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_249) then 18 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_652) then 13 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_304) then 3 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 3 4 5 6 240
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 0 5 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 496
cert_cover_5 4 2 3 4 5 7 240 496 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0080

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_multi_six_0081.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0081

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 341, 681, 817, 206, 650, 962, 252, 496, 928, 7, 11, 259, 21, 325, 41, 521, 49, 273, 545, 769, 14, 70, 138, 522, 194, 322, 642, 770, 60, 204, 84, 168, 648, 240, 304, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_341, vertices_681, vertices_817, vertices_206, vertices_650, vertices_962, vertices_252, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_325, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_138, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_60, vertices_204, vertices_84, vertices_168, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_341), (false, vertices_681), (false, vertices_817), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_204), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 12 8 15 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 9 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_779) then 7 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_681) then 10 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_204) then 11 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_416) then 3 else
  if p.val = (true, vertices_448) then 4 else
  if p.val = (true, vertices_896) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 8 => Sum.inl 2
  | 9 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 2 3 5 4 252 60 3
cert_row_4 2 1 2 3 5 6 252 60 3
cert_rows_3
cert_pivot_3 4 0 1
cert_heightProof 3
cert_coverFacet 0 206
cert_cover 0 2 2 0 1 3 1 5 3 14 206 204 60 252 5
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 252
cert_cover_2 3 2 1 3 5 60 252 3
cert_coverFacet 4 496
cert_cover 4 5 2 3 4 3 1 7 3 240 496 240 60 252 5
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0081

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_multi_six_0082.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0082

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 651, 771, 341, 553, 817, 206, 962, 252, 936, 496, 7, 11, 259, 515, 21, 325, 41, 521, 49, 273, 545, 769, 14, 70, 138, 194, 322, 642, 770, 60, 204, 84, 168, 552, 648, 240, 304, 336, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_651, vertices_771, vertices_341, vertices_553, vertices_817, vertices_206, vertices_962, vertices_252, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_21, vertices_325, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_60, vertices_204, vertices_84, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_651), (false, vertices_771), (false, vertices_341), (false, vertices_553), (false, vertices_817), (true, vertices_194), (true, vertices_204), (true, vertices_168), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 12 9 15 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_651) then 8 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_204) then 11 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_896) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 2 4 6 7 8 936 168 3
cert_row_4 2 1 2 3 5 4 252 60 3
cert_row_4 3 1 2 3 5 6 252 60 3
cert_rows
cert_pivot_2 0 7 4 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover 0 2 2 0 1 3 1 5 3 14 206 204 60 252 5
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 252
cert_cover_2 2 2 1 3 5 60 252 3
cert_coverFacet 3 936
cert_cover_5 3 1 2 4 6 7 168 936 3
cert_coverFacet 4 496
cert_cover 4 5 2 3 4 3 1 7 3 240 496 240 60 252 5
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0082

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0570 : Certifies 570 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0048.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0571 : Certifies 571 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0049.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0572 : Certifies 572 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0050.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0573 : Certifies 573 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0054.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0574 : Certifies 574 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0055.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0575 : Certifies 575 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0056.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0576 : Certifies 576 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0577 : Certifies 577 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0578 : Certifies 578 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0059.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0579 : Certifies 579 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0060.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0580 : Certifies 580 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0061.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0581 : Certifies 581 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0062.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0582 : Certifies 582 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0583 : Certifies 583 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0584 : Certifies 584 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0065.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0585 : Certifies 585 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0066.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0586 : Certifies 586 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0068.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0587 : Certifies 587 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0070.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0588 : Certifies 588 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0589 : Certifies 589 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0072.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0590 : Certifies 590 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0073.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0591 : Certifies 591 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0074.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0592 : Certifies 592 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0075.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0593 : Certifies 593 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0076.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0594 : Certifies 594 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0077.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0595 : Certifies 595 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0078.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0596 : Certifies 596 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0079.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0597 : Certifies 597 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0080.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0598 : Certifies 598 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0081.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0599 : Certifies 599 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0082.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B019 (j : Fin 30) :
    Certifies (570 + j.val) := by
  fin_cases j
  · exact projection_0570
  · exact projection_0571
  · exact projection_0572
  · exact projection_0573
  · exact projection_0574
  · exact projection_0575
  · exact projection_0576
  · exact projection_0577
  · exact projection_0578
  · exact projection_0579
  · exact projection_0580
  · exact projection_0581
  · exact projection_0582
  · exact projection_0583
  · exact projection_0584
  · exact projection_0585
  · exact projection_0586
  · exact projection_0587
  · exact projection_0588
  · exact projection_0589
  · exact projection_0590
  · exact projection_0591
  · exact projection_0592
  · exact projection_0593
  · exact projection_0594
  · exact projection_0595
  · exact projection_0596
  · exact projection_0597
  · exact projection_0598
  · exact projection_0599

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
