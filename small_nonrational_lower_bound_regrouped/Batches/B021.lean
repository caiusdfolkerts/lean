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
/- Source: ProjectionCertificates/R_multi_six_0114.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0114

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 245, 425, 526, 906, 962, 540, 852, 824, 496, 7, 11, 67, 53, 69, 41, 137, 161, 193, 14, 518, 138, 522, 194, 578, 898, 28, 524, 84, 532, 580, 56, 536, 296, 392, 776, 240, 304, 336, 784, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_245, vertices_425, vertices_526, vertices_906, vertices_962, vertices_540, vertices_852, vertices_824, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_53, vertices_69, vertices_41, vertices_137, vertices_161, vertices_193, vertices_14, vertices_518, vertices_138, vertices_522, vertices_194, vertices_578, vertices_898, vertices_28, vertices_524, vertices_84, vertices_532, vertices_580, vertices_56, vertices_536, vertices_296, vertices_392, vertices_776, vertices_240, vertices_304, vertices_336, vertices_784, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_245), (false, vertices_425), (true, vertices_522), (true, vertices_898), (true, vertices_524), (true, vertices_532), (true, vertices_536), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 10 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 11 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_245) then 19 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_898) then 15 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_245), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 6 7 8 898
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 496
cert_cover_5 6 1 3 4 5 7 240 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0114

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_multi_six_0115.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0115

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 597, 249, 398, 202, 962, 428, 820, 496, 848, 7, 11, 515, 21, 517, 57, 73, 81, 577, 14, 262, 74, 138, 194, 578, 386, 770, 44, 396, 52, 532, 292, 772, 168, 200, 240, 304, 336, 592, 784, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_597, vertices_249, vertices_398, vertices_202, vertices_962, vertices_428, vertices_820, vertices_496, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_577, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_396, vertices_52, vertices_532, vertices_292, vertices_772, vertices_168, vertices_200, vertices_240, vertices_304, vertices_336, vertices_592, vertices_784, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_597), (false, vertices_249), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_292), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 3 4 5 6 240
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 0 5 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 496
cert_cover_5 5 2 3 4 5 7 240 496 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0115

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_multi_six_0116.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0116

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 781, 645, 961, 662, 250, 300, 820, 488, 944, 7, 11, 67, 13, 133, 517, 265, 193, 321, 641, 769, 22, 134, 58, 74, 146, 194, 44, 268, 52, 532, 292, 644, 772, 232, 296, 328, 176, 816, 656, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_781, vertices_645, vertices_961, vertices_662, vertices_250, vertices_300, vertices_820, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_517, vertices_265, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_146, vertices_194, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_644, vertices_772, vertices_232, vertices_296, vertices_328, vertices_176, vertices_816, vertices_656, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_781), (false, vertices_645), (false, vertices_961), (true, vertices_146), (true, vertices_532), (true, vertices_292), (true, vertices_232), (true, vertices_296), (true, vertices_176), (true, vertices_816), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_331) then 10 else
  if p.val = (false, vertices_781) then 13 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_232) then 15 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_416) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
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
cert_row_4 1 0 1 3 6 8 662 22 3
cert_row_4 2 0 2 3 5 4 250 58 3
cert_row_4 3 0 2 3 5 6 250 58 3
cert_rows
cert_pivot_2 7 1 4 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 22 662 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 488
cert_cover 4 5 2 2 4 3 0 7 3 232 488 232 58 250 5
cert_coverFacet 5 944
cert_cover_5 5 0 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0116

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_multi_six_0117.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0117

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 333, 961, 662, 250, 706, 300, 820, 488, 944, 7, 11, 515, 13, 261, 73, 321, 577, 769, 22, 518, 58, 74, 146, 194, 578, 642, 44, 268, 52, 532, 292, 772, 232, 296, 328, 176, 816, 656, 416, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_333, vertices_961, vertices_662, vertices_250, vertices_706, vertices_300, vertices_820, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_13, vertices_261, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_518, vertices_58, vertices_74, vertices_146, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_232, vertices_296, vertices_328, vertices_176, vertices_816, vertices_656, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_333), (false, vertices_961), (true, vertices_146), (true, vertices_194), (true, vertices_642), (true, vertices_532), (true, vertices_292), (true, vertices_232), (true, vertices_296), (true, vertices_176), (true, vertices_816), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_333) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_232) then 16 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 3 6 8 662 22 3
cert_row_4 2 0 2 3 5 4 250 58 3
cert_row_4 3 0 2 3 5 6 250 58 3
cert_rows
cert_pivot_2 7 1 4 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 22 662 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 488
cert_cover 5 5 2 2 4 3 0 7 3 232 488 232 58 250 5
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0117

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_multi_six_0118.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0118

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 331, 781, 961, 662, 250, 706, 300, 820, 488, 944, 7, 11, 67, 13, 517, 265, 321, 577, 769, 22, 518, 58, 74, 146, 194, 578, 642, 44, 268, 52, 532, 292, 772, 232, 296, 328, 176, 816, 656, 416, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_331, vertices_781, vertices_961, vertices_662, vertices_250, vertices_706, vertices_300, vertices_820, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_265, vertices_321, vertices_577, vertices_769, vertices_22, vertices_518, vertices_58, vertices_74, vertices_146, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_232, vertices_296, vertices_328, vertices_176, vertices_816, vertices_656, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_331), (false, vertices_781), (false, vertices_961), (true, vertices_146), (true, vertices_194), (true, vertices_642), (true, vertices_532), (true, vertices_292), (true, vertices_232), (true, vertices_296), (true, vertices_176), (true, vertices_816), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_232) then 16 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 3 6 8 662 22 3
cert_row_4 2 0 2 3 5 4 250 58 3
cert_row_4 3 0 2 3 5 6 250 58 3
cert_rows
cert_pivot_2 7 1 4 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 22 662 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 488
cert_cover 5 5 2 2 4 3 0 7 3 232 488 232 58 250 5
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0118

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_multi_six_0119.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0119

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 661, 809, 561, 78, 710, 962, 252, 488, 944, 7, 11, 259, 21, 517, 41, 265, 49, 529, 545, 769, 14, 70, 518, 74, 706, 322, 770, 60, 76, 148, 196, 644, 232, 296, 328, 176, 560, 656, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_661, vertices_809, vertices_561, vertices_78, vertices_710, vertices_962, vertices_252, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_769, vertices_14, vertices_70, vertices_518, vertices_74, vertices_706, vertices_322, vertices_770, vertices_60, vertices_76, vertices_148, vertices_196, vertices_644, vertices_232, vertices_296, vertices_328, vertices_176, vertices_560, vertices_656, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_661), (false, vertices_809), (false, vertices_561), (true, vertices_70), (true, vertices_706), (true, vertices_76), (true, vertices_196), (true, vertices_232), (true, vertices_176), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 15 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_661) then 10 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_706) then 14 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_232) then 17 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 8 706
cert_row_4 1 3 4 6 7 8 944 176 3
cert_row_4 2 1 2 3 5 4 252 60 3
cert_row_4 3 1 2 3 5 6 252 60 3
cert_rows
cert_pivot_2 0 7 4 1
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 70 710 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 706 962 3
cert_coverFacet 3 252
cert_cover_2 3 2 1 3 5 60 252 3
cert_coverFacet 4 488
cert_cover 4 5 2 2 4 3 1 7 3 232 488 232 60 252 5
cert_coverFacet 5 944
cert_cover_5 5 1 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0119

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_multi_six_0120.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0120

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 331, 661, 249, 705, 782, 962, 812, 564, 488, 944, 7, 11, 67, 21, 517, 57, 73, 145, 193, 577, 641, 14, 518, 266, 322, 578, 770, 44, 780, 52, 532, 548, 232, 296, 328, 176, 560, 656, 416, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_331, vertices_661, vertices_249, vertices_705, vertices_782, vertices_962, vertices_812, vertices_564, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_517, vertices_57, vertices_73, vertices_145, vertices_193, vertices_577, vertices_641, vertices_14, vertices_518, vertices_266, vertices_322, vertices_578, vertices_770, vertices_44, vertices_780, vertices_52, vertices_532, vertices_548, vertices_232, vertices_296, vertices_328, vertices_176, vertices_560, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_331), (false, vertices_661), (false, vertices_249), (false, vertices_705), (true, vertices_770), (true, vertices_780), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_661) then 13 else
  if p.val = (false, vertices_249) then 18 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_780) then 14 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
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
cert_row_2 0 1 2 7 8 780
cert_row_2 1 2 4 5 6 232
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 322 962 2
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 488
cert_cover_5 4 1 2 4 5 7 232 488 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0120

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_multi_six_0121.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0121

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 661, 249, 782, 646, 962, 812, 564, 488, 944, 7, 11, 67, 21, 133, 57, 73, 145, 193, 14, 134, 518, 266, 194, 322, 642, 770, 44, 780, 52, 532, 548, 644, 232, 296, 328, 176, 560, 656, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_661, vertices_249, vertices_782, vertices_646, vertices_962, vertices_812, vertices_564, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_57, vertices_73, vertices_145, vertices_193, vertices_14, vertices_134, vertices_518, vertices_266, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_780, vertices_52, vertices_532, vertices_548, vertices_644, vertices_232, vertices_296, vertices_328, vertices_176, vertices_560, vertices_656, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_661), (false, vertices_249), (true, vertices_518), (true, vertices_642), (true, vertices_770), (true, vertices_780), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_780) then 15 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
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
cert_row_2 0 1 2 7 8 780
cert_row_2 1 2 4 5 6 232
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 194 962 3
cert_coverFacet 3 812
cert_cover_5 3 0 1 2 4 7 44 812 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 488
cert_cover_5 5 1 2 4 5 7 232 488 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0121

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_multi_six_0124.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0124

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 269, 905, 278, 122, 722, 914, 812, 884, 744, 7, 11, 131, 13, 261, 137, 265, 385, 22, 262, 58, 74, 82, 658, 274, 194, 386, 44, 268, 52, 276, 804, 104, 552, 200, 648, 776, 112, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_269, vertices_905, vertices_278, vertices_122, vertices_722, vertices_914, vertices_812, vertices_884, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_261, vertices_137, vertices_265, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_658, vertices_274, vertices_194, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_804, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_269), (false, vertices_905), (true, vertices_82), (true, vertices_658), (true, vertices_274), (true, vertices_276), (true, vertices_804), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_905) then 19 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_658) then 17 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_804) then 13 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_658), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 7 884 52 3
cert_row_4 1 1 3 4 5 8 884 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_2 3 0 3 6 8 658
cert_row_2 4 0 2 3 4 58
cert_rows_2
cert_pivot 7 1 5 6 0
cert_heightProof 5
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 122
cert_cover_5 1 4 0 2 3 5 58 122 3
cert_coverFacet 2 722
cert_cover_5 2 3 0 3 5 6 82 722 3
cert_coverFacet 3 914
cert_cover_5 3 3 0 3 6 7 658 914 3
cert_coverFacet 4 812
cert_cover 4 4 3 1 2 3 1 7 4 44 812 804 52 884 5
cert_coverFacet 5 884
cert_cover_2 5 3 1 4 5 52 884 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 104 744 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0124

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_multi_six_0125.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0125

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 620, 564, 712, 1008, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 200, 584, 648, 112, 560, 464, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_620, vertices_564, vertices_712, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_560, vertices_464, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 8 18 11 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_789) then 10 else
  if p.val = (false, vertices_121) then 13 else
  if p.val = (false, vertices_465) then 14 else
  if p.val = (true, vertices_778) then 17 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_584) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 3 4 5 6 7 1008 112 3
cert_row_4 3 3 4 5 6 8 1008 112 3
cert_rows
cert_pivot_2 0 1 7 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 712
cert_cover_2 4 5 2 6 8 200 712 3
cert_coverFacet 5 1008
cert_cover_2 5 4 3 5 6 112 1008 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0125

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_multi_six_0126.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0126

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 405, 121, 721, 270, 906, 812, 884, 744, 912, 7, 11, 131, 21, 389, 57, 73, 81, 145, 193, 14, 262, 138, 266, 386, 44, 268, 52, 276, 804, 104, 552, 200, 648, 776, 112, 592, 400, 656, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_405, vertices_121, vertices_721, vertices_270, vertices_906, vertices_812, vertices_884, vertices_744, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_389, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_804, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_400, vertices_656, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_405), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_804), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_784), (true, vertices_608), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 17 10 13 15 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_203) then 9 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_121) then 12 else
  if p.val = (false, vertices_721) then 14 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_804) then 16 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 15 => Sum.inl 4
  | 16 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 3 4 5 7 884 52 3
cert_row_4 2 1 3 4 5 8 884 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover 2 4 3 1 2 3 1 7 4 44 812 804 52 884 5
cert_coverFacet 3 884
cert_cover_2 3 3 1 4 5 52 884 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 912
cert_cover_2 5 6 3 7 8 400 912 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0126

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_multi_six_0128.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0128

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 789, 361, 305, 206, 458, 898, 124, 724, 1008, 7, 11, 515, 21, 517, 41, 265, 49, 273, 289, 769, 14, 134, 202, 266, 386, 642, 770, 60, 76, 84, 532, 196, 644, 104, 328, 112, 304, 720, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_789, vertices_361, vertices_305, vertices_206, vertices_458, vertices_898, vertices_124, vertices_724, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_273, vertices_289, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_532, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_304, vertices_720, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_789), (false, vertices_361), (false, vertices_305), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_720), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 8 17 11 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_647) then 9 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_789) then 10 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_720) then 13 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 3 4 5 6 7 1008 112 3
cert_row_4 3 3 4 5 6 8 1008 112 3
cert_rows
cert_pivot_2 0 1 7 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 724
cert_cover 4 5 4 1 3 3 3 6 5 84 724 720 112 1008 6
cert_coverFacet 5 1008
cert_cover_2 5 4 3 5 6 112 1008 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0128

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_multi_six_0129.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0129

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 903, 779, 213, 553, 689, 206, 458, 124, 872, 496, 928, 7, 11, 771, 21, 133, 41, 521, 49, 145, 545, 641, 14, 134, 202, 266, 386, 60, 76, 84, 196, 104, 552, 328, 776, 112, 176, 208, 352, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_903, vertices_779, vertices_213, vertices_553, vertices_689, vertices_206, vertices_458, vertices_124, vertices_872, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_771, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_641, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_176, vertices_208, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_903), (false, vertices_779), (false, vertices_213), (false, vertices_553), (false, vertices_689), (true, vertices_202), (true, vertices_76), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_352), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 9 18 11 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_903) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_213) then 10 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_689) then 13 else
  if p.val = (true, vertices_202) then 17 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_903), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 872
cert_cover_5 3 2 2 4 5 7 104 872 3
cert_coverFacet 4 496
cert_cover_5 4 3 3 4 5 6 112 496 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0129

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_multi_six_0130.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0130

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 903, 779, 213, 553, 689, 206, 458, 124, 872, 624, 976, 7, 11, 771, 21, 133, 41, 521, 49, 145, 545, 641, 14, 134, 202, 266, 386, 60, 76, 84, 196, 104, 552, 328, 776, 112, 560, 208, 592, 656, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_903, vertices_779, vertices_213, vertices_553, vertices_689, vertices_206, vertices_458, vertices_124, vertices_872, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_771, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_641, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_903), (false, vertices_779), (false, vertices_213), (false, vertices_553), (false, vertices_689), (true, vertices_202), (true, vertices_76), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 9 18 11 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_903) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_213) then 10 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_689) then 13 else
  if p.val = (true, vertices_202) then 17 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_903), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 872
cert_cover_5 3 2 2 4 5 7 104 872 3
cert_coverFacet 4 624
cert_cover_2 4 4 3 5 8 112 624 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0130

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_multi_six_0135.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0135

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 331, 195, 661, 249, 782, 962, 364, 820, 368, 976, 7, 11, 67, 131, 21, 645, 57, 73, 145, 193, 14, 518, 266, 194, 322, 642, 770, 44, 268, 52, 532, 292, 772, 104, 328, 112, 304, 208, 336, 656, 784, 352, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_331, vertices_195, vertices_661, vertices_249, vertices_782, vertices_962, vertices_364, vertices_820, vertices_368, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_645, vertices_57, vertices_73, vertices_145, vertices_193, vertices_14, vertices_518, vertices_266, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_328, vertices_112, vertices_304, vertices_208, vertices_336, vertices_656, vertices_784, vertices_352, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_331), (false, vertices_195), (false, vertices_661), (false, vertices_249), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_352), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 14 16 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_331) then 10 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_661) then 13 else
  if p.val = (false, vertices_249) then 17 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_960) then 20 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 5 6 7 8 960
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 364
cert_cover_5 2 2 1 2 4 5 44 364 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 368
cert_cover_2 4 4 3 5 7 112 368 3
cert_coverFacet 5 976
cert_cover_5 5 0 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0135

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_multi_six_0136.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0136

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 331, 195, 661, 249, 782, 962, 364, 820, 880, 720, 7, 11, 67, 131, 21, 645, 57, 73, 145, 193, 14, 518, 266, 194, 322, 642, 770, 44, 268, 52, 532, 292, 772, 104, 328, 112, 816, 208, 592, 656, 352, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_331, vertices_195, vertices_661, vertices_249, vertices_782, vertices_962, vertices_364, vertices_820, vertices_880, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_645, vertices_57, vertices_73, vertices_145, vertices_193, vertices_14, vertices_518, vertices_266, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_328, vertices_112, vertices_816, vertices_208, vertices_592, vertices_656, vertices_352, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_331), (false, vertices_195), (false, vertices_661), (false, vertices_249), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_816), (true, vertices_592), (true, vertices_352), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 14 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_331) then 10 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_661) then 13 else
  if p.val = (false, vertices_249) then 17 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 364
cert_cover_5 2 3 1 2 4 5 44 364 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 880
cert_cover_5 4 0 3 4 5 7 112 880 3
cert_coverFacet 5 720
cert_cover_2 5 5 3 6 8 208 720 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0136

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_multi_six_0138.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0138

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 331, 451, 661, 249, 782, 898, 556, 628, 872, 976, 7, 11, 323, 131, 21, 645, 57, 73, 145, 193, 14, 518, 266, 386, 642, 770, 44, 524, 52, 532, 548, 104, 552, 328, 776, 112, 208, 592, 656, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_331, vertices_451, vertices_661, vertices_249, vertices_782, vertices_898, vertices_556, vertices_628, vertices_872, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_323, vertices_131, vertices_21, vertices_645, vertices_57, vertices_73, vertices_145, vertices_193, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_208, vertices_592, vertices_656, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_331), (false, vertices_451), (false, vertices_661), (false, vertices_249), (true, vertices_770), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_776), (true, vertices_592), (true, vertices_608), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 9 15 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 10 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_661) then 11 else
  if p.val = (false, vertices_249) then 18 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_832) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 14 3
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 52 628 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0138

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_multi_six_0145.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0145

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 341, 249, 782, 650, 962, 684, 820, 1008, 7, 11, 67, 21, 325, 57, 201, 81, 14, 262, 138, 522, 194, 322, 642, 770, 44, 524, 52, 276, 548, 772, 168, 648, 240, 816, 336, 672, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_341, vertices_249, vertices_782, vertices_650, vertices_962, vertices_684, vertices_820, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_325, vertices_57, vertices_201, vertices_81, vertices_14, vertices_262, vertices_138, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_648, vertices_240, vertices_816, vertices_336, vertices_672, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_341), (false, vertices_249), (true, vertices_522), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_648), (true, vertices_816), (true, vertices_672), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 9 12 15 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_341) then 11 else
  if p.val = (false, vertices_249) then 16 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_960) then 20 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 3 4 5 7 6 1008 240 3
cert_row_4 3 3 4 5 7 8 1008 240 3
cert_rows
cert_pivot_2 0 1 6 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 962
cert_cover 2 6 4 0 5 3 3 7 5 194 962 960 240 1008 7
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover 4 4 4 1 3 3 3 7 5 52 820 816 240 1008 7
cert_coverFacet 5 1008
cert_cover_2 5 4 3 5 7 240 1008 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0145

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_multi_six_0146.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0146

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 853, 249, 654, 962, 812, 308, 936, 496, 7, 11, 67, 21, 581, 57, 201, 81, 14, 518, 138, 194, 578, 642, 44, 524, 52, 276, 292, 772, 168, 808, 648, 240, 304, 336, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_853, vertices_249, vertices_654, vertices_962, vertices_812, vertices_308, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_581, vertices_57, vertices_201, vertices_81, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_168, vertices_808, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_853), (false, vertices_249), (true, vertices_642), (true, vertices_524), (true, vertices_292), (true, vertices_808), (true, vertices_648), (true, vertices_304), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 9 14 11 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_853) then 13 else
  if p.val = (false, vertices_249) then 16 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_808) then 17 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_853), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_2 1 2 4 7 8 808
cert_row_4 2 0 1 2 6 8 654 14 3
cert_row_4 3 0 5 6 7 8 962 194 3
cert_rows
cert_pivot_2 3 4 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 3 0 5 6 7 194 962 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 936
cert_cover_5 4 1 2 4 6 7 168 936 3
cert_coverFacet 5 496
cert_cover_5 5 0 3 4 5 7 240 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0146

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_multi_six_0147.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0147

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 341, 249, 654, 202, 962, 684, 820, 1008, 7, 11, 259, 21, 261, 57, 73, 81, 321, 14, 518, 74, 138, 194, 322, 642, 770, 44, 652, 52, 276, 548, 772, 168, 200, 240, 816, 336, 672, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_341, vertices_249, vertices_654, vertices_202, vertices_962, vertices_684, vertices_820, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_74, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_200, vertices_240, vertices_816, vertices_336, vertices_672, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_341), (false, vertices_249), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_816), (true, vertices_672), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 5 8 11 13 16 17 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 6 else
  if p.val = (false, vertices_331) then 7 else
  if p.val = (false, vertices_341) then 9 else
  if p.val = (false, vertices_249) then 14 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_652) then 10 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_816) then 15 else
  if p.val = (true, vertices_672) then 4 else
  if p.val = (true, vertices_960) then 18 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 5 => Sum.inl 0
  | 6 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 3 4 5 7 6 1008 240 3
cert_row_4 2 3 4 5 7 8 1008 240 3
cert_rows_3
cert_pivot_3 6 1 3
cert_heightProof 3
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover 2 6 4 0 5 3 3 7 5 194 962 960 240 1008 7
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover 4 4 4 1 3 3 3 7 5 52 820 816 240 1008 7
cert_coverFacet 5 1008
cert_cover_2 5 4 3 5 7 240 1008 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0147

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_multi_six_0148.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0148

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 277, 249, 465, 590, 962, 748, 820, 944, 7, 11, 259, 21, 261, 57, 73, 209, 273, 321, 14, 518, 74, 322, 578, 770, 44, 588, 52, 276, 548, 772, 232, 176, 816, 400, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_277, vertices_249, vertices_465, vertices_590, vertices_962, vertices_748, vertices_820, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_209, vertices_273, vertices_321, vertices_14, vertices_518, vertices_74, vertices_322, vertices_578, vertices_770, vertices_44, vertices_588, vertices_52, vertices_276, vertices_548, vertices_772, vertices_232, vertices_176, vertices_816, vertices_400, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_277), (false, vertices_249), (false, vertices_465), (true, vertices_578), (true, vertices_588), (true, vertices_548), (true, vertices_816), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 11 13 17 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 7 else
  if p.val = (false, vertices_331) then 8 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_249) then 14 else
  if p.val = (false, vertices_465) then 15 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_588) then 10 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_816) then 16 else
  if p.val = (true, vertices_672) then 3 else
  if p.val = (true, vertices_704) then 4 else
  if p.val = (true, vertices_896) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 1 2 4 5 6 748 44 3
cert_row_4 3 1 2 4 5 8 748 44 3
cert_rows
cert_pivot_2 3 0 6 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover 0 2 2 0 1 3 1 5 4 14 590 588 44 748 5
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 322 962 2
cert_coverFacet 2 748
cert_cover_2 2 2 1 4 5 44 748 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 944
cert_cover_5 4 0 3 4 6 7 176 944 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0148

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_multi_six_0149.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0149

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 789, 249, 721, 334, 962, 492, 308, 944, 7, 11, 515, 21, 773, 57, 73, 209, 529, 577, 14, 262, 74, 322, 578, 770, 44, 332, 52, 276, 292, 232, 176, 304, 656, 784, 416, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_789, vertices_249, vertices_721, vertices_334, vertices_962, vertices_492, vertices_308, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_773, vertices_57, vertices_73, vertices_209, vertices_529, vertices_577, vertices_14, vertices_262, vertices_74, vertices_322, vertices_578, vertices_770, vertices_44, vertices_332, vertices_52, vertices_276, vertices_292, vertices_232, vertices_176, vertices_304, vertices_656, vertices_784, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_789), (false, vertices_249), (false, vertices_721), (true, vertices_322), (true, vertices_332), (true, vertices_292), (true, vertices_304), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 11 8 14 17 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 9 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_587) then 7 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_249) then 15 else
  if p.val = (false, vertices_721) then 16 else
  if p.val = (true, vertices_322) then 0 else
  if p.val = (true, vertices_332) then 10 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_304) then 2 else
  if p.val = (true, vertices_416) then 3 else
  if p.val = (true, vertices_448) then 4 else
  if p.val = (true, vertices_896) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 8 => Sum.inl 2
  | 9 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 322 2
cert_row_4 1 3 4 6 7 8 944 176 3
cert_row_4 2 1 2 4 5 6 492 44 3
cert_row_4 3 1 2 4 5 7 492 44 3
cert_rows
cert_pivot_2 0 3 6 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover 0 2 2 0 1 3 1 5 4 14 334 332 44 492 5
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 322 962 2
cert_coverFacet 2 492
cert_cover_2 2 2 1 4 5 44 492 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 944
cert_cover_5 4 1 3 4 6 7 176 944 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0149

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_multi_six_0150.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0150

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 839, 395, 597, 297, 817, 206, 962, 252, 936, 752, 7, 11, 259, 21, 581, 41, 265, 49, 529, 289, 769, 14, 70, 138, 194, 834, 386, 60, 204, 84, 168, 296, 392, 240, 560, 592, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_839, vertices_395, vertices_597, vertices_297, vertices_817, vertices_206, vertices_962, vertices_252, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_581, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_834, vertices_386, vertices_60, vertices_204, vertices_84, vertices_168, vertices_296, vertices_392, vertices_240, vertices_560, vertices_592, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_839), (false, vertices_395), (false, vertices_597), (false, vertices_297), (false, vertices_817), (true, vertices_194), (true, vertices_204), (true, vertices_168), (true, vertices_240), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 11 8 14 17 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 9 else
  if p.val = (false, vertices_839) then 12 else
  if p.val = (false, vertices_395) then 7 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_204) then 10 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_240) then 16 else
  if p.val = (true, vertices_672) then 3 else
  if p.val = (true, vertices_704) then 4 else
  if p.val = (true, vertices_896) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 8 => Sum.inl 2
  | 9 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_839), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
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
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 252
cert_cover_2 2 2 1 3 5 60 252 3
cert_coverFacet 3 936
cert_cover_5 3 1 2 4 6 7 168 936 3
cert_coverFacet 4 752
cert_cover 4 5 2 3 4 3 1 8 3 240 752 240 60 252 5
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0150

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_multi_six_0151.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0151

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 533, 249, 849, 654, 962, 940, 820, 496, 7, 11, 67, 21, 517, 57, 201, 81, 529, 577, 14, 518, 138, 194, 578, 642, 44, 652, 52, 532, 804, 168, 240, 304, 336, 784, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_533, vertices_249, vertices_849, vertices_654, vertices_962, vertices_940, vertices_820, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_517, vertices_57, vertices_201, vertices_81, vertices_529, vertices_577, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_652, vertices_52, vertices_532, vertices_804, vertices_168, vertices_240, vertices_304, vertices_336, vertices_784, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_533), (false, vertices_249), (false, vertices_849), (true, vertices_642), (true, vertices_652), (true, vertices_804), (true, vertices_304), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 8 11 14 17 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_583) then 7 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_249) then 15 else
  if p.val = (false, vertices_849) then 16 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_652) then 9 else
  if p.val = (true, vertices_804) then 10 else
  if p.val = (true, vertices_304) then 2 else
  if p.val = (true, vertices_416) then 3 else
  if p.val = (true, vertices_448) then 4 else
  if p.val = (true, vertices_896) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 1 2 4 6 7 940 44 3
cert_row_4 3 1 2 4 6 8 940 44 3
cert_rows
cert_pivot_2 3 0 7 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover 0 2 2 0 1 3 1 6 4 14 654 652 44 940 6
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 940
cert_cover_2 2 2 1 4 6 44 940 3
cert_coverFacet 3 820
cert_cover 3 4 2 1 3 3 1 7 4 52 820 804 44 940 6
cert_coverFacet 4 496
cert_cover_5 4 0 3 4 5 7 240 496 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0151

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_multi_six_0152.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0152

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 455, 779, 245, 425, 590, 962, 604, 824, 752, 928, 7, 11, 259, 53, 197, 41, 265, 161, 385, 14, 70, 522, 450, 578, 770, 28, 588, 84, 56, 536, 296, 776, 240, 560, 592, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_455, vertices_779, vertices_245, vertices_425, vertices_590, vertices_962, vertices_604, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_197, vertices_41, vertices_265, vertices_161, vertices_385, vertices_14, vertices_70, vertices_522, vertices_450, vertices_578, vertices_770, vertices_28, vertices_588, vertices_84, vertices_56, vertices_536, vertices_296, vertices_776, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_455), (false, vertices_779), (false, vertices_245), (false, vertices_425), (true, vertices_578), (true, vertices_588), (true, vertices_536), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 13 10 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_455) then 15 else
  if p.val = (false, vertices_779) then 9 else
  if p.val = (false, vertices_245) then 17 else
  if p.val = (false, vertices_425) then 11 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_588) then 12 else
  if p.val = (true, vertices_536) then 1 else
  if p.val = (true, vertices_560) then 2 else
  if p.val = (true, vertices_592) then 3 else
  if p.val = (true, vertices_672) then 4 else
  if p.val = (true, vertices_800) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_455), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_245), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_2 1 0 5 6 7 450
cert_row_2 2 3 4 5 6 240
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 0 5 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 8 450 962 3
cert_coverFacet 2 604
cert_cover_5 2 0 1 2 3 5 28 604 3
cert_coverFacet 3 824
cert_cover_5 3 3 2 3 4 7 56 824 3
cert_coverFacet 4 752
cert_cover_5 4 2 3 4 5 8 240 752 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0152

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_multi_six_0154.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0154

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 977, 782, 906, 556, 628, 744, 7, 11, 131, 21, 261, 57, 73, 81, 785, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 592, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_977, vertices_782, vertices_906, vertices_556, vertices_628, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_785, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_592, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_977), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 5 13 14 7 16 18 19 20
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 8 else
  if p.val = (false, vertices_391) then 6 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 9 else
  if p.val = (false, vertices_977) then 17 else
  if p.val = (true, vertices_778) then 12 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_608) then 4 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 5 => Sum.inl 1
  | 6 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 7 => Sum.inl 4
  | 8 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 5
  | 17 => Sum.inr ⟨(false, vertices_977), by decide +kernel⟩
  | 18 => Sum.inl 6
  | 19 => Sum.inl 7
  | 20 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_rows_3
cert_pivot_3 1 0 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 52 628 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 3 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0154

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_multi_six_0163.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0163

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 917, 121, 721, 270, 906, 812, 628, 744, 7, 11, 131, 21, 389, 57, 73, 81, 657, 193, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 592, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_917, vertices_121, vertices_721, vertices_270, vertices_906, vertices_812, vertices_628, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_389, vertices_57, vertices_73, vertices_81, vertices_657, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_917), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 9 11 14 17 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 8 else
  if p.val = (false, vertices_917) then 15 else
  if p.val = (false, vertices_121) then 13 else
  if p.val = (false, vertices_721) then 16 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_608) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_917), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0163

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_multi_six_0169.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0169

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 977, 270, 906, 812, 628, 744, 7, 11, 131, 21, 261, 57, 73, 81, 785, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 592, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_977, vertices_270, vertices_906, vertices_812, vertices_628, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_785, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_977), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 11 14 16 17 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 8 else
  if p.val = (false, vertices_203) then 9 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 13 else
  if p.val = (false, vertices_977) then 18 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_608) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inr ⟨(false, vertices_977), by decide +kernel⟩
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0169

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_multi_six_0170.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0170

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 625, 961, 398, 842, 450, 444, 600, 792, 944, 7, 27, 67, 37, 133, 49, 81, 545, 193, 577, 641, 14, 134, 74, 266, 194, 322, 386, 60, 396, 164, 88, 280, 536, 584, 776, 432, 560, 592, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_625, vertices_961, vertices_398, vertices_842, vertices_450, vertices_444, vertices_600, vertices_792, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_134, vertices_74, vertices_266, vertices_194, vertices_322, vertices_386, vertices_60, vertices_396, vertices_164, vertices_88, vertices_280, vertices_536, vertices_584, vertices_776, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_625), (false, vertices_961), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_396), (true, vertices_280), (true, vertices_536), (true, vertices_584), (true, vertices_776), (true, vertices_432), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 16 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_677) then 13 else
  if p.val = (false, vertices_625) then 17 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_396) then 14 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
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
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 1 2 3 6 4 444 60 3
cert_row_4 2 1 2 3 6 7 444 60 3
cert_rows_3
cert_pivot_3 4 0 1
cert_heightProof 3
cert_coverFacet 0 398
cert_cover 0 2 2 0 1 3 1 6 3 14 398 396 60 444 6
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 444
cert_cover_2 3 2 1 3 6 60 444 3
cert_coverFacet 4 600
cert_cover_2 4 3 2 5 8 88 600 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 944
cert_cover 6 6 2 3 4 3 1 8 3 432 944 432 60 444 6
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0170

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_multi_six_0171.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0171

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 429, 841, 625, 929, 398, 214, 330, 962, 116, 740, 27, 45, 73, 265, 49, 81, 417, 545, 577, 769, 14, 22, 134, 74, 266, 82, 194, 322, 386, 396, 52, 84, 100, 164, 196, 328, 112, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_429, vertices_841, vertices_625, vertices_929, vertices_398, vertices_214, vertices_330, vertices_962, vertices_116, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_265, vertices_49, vertices_81, vertices_417, vertices_545, vertices_577, vertices_769, vertices_14, vertices_22, vertices_134, vertices_74, vertices_266, vertices_82, vertices_194, vertices_322, vertices_386, vertices_396, vertices_52, vertices_84, vertices_100, vertices_164, vertices_196, vertices_328, vertices_112, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_429), (false, vertices_841), (false, vertices_625), (false, vertices_929), (true, vertices_134), (true, vertices_266), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_84), (true, vertices_100), (true, vertices_196), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 13 15 17 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_429) then 18 else
  if p.val = (false, vertices_841) then 14 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_929) then 19 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_429), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 1 3 5 6 214 22 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 5 22 214 3
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 194 962 3
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 740
cert_cover_5 5 3 1 4 5 6 100 740 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0171

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0630 : Certifies 630 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0114.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0631 : Certifies 631 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0115.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0632 : Certifies 632 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0116.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0633 : Certifies 633 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0117.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0634 : Certifies 634 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0118.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0635 : Certifies 635 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0119.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0636 : Certifies 636 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0120.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0637 : Certifies 637 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0121.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0638 : Certifies 638 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0124.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0639 : Certifies 639 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0125.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0640 : Certifies 640 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0126.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0641 : Certifies 641 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0128.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0642 : Certifies 642 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0129.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0643 : Certifies 643 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0130.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0644 : Certifies 644 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0135.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0645 : Certifies 645 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0136.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0646 : Certifies 646 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0138.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0647 : Certifies 647 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0145.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0648 : Certifies 648 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0146.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0649 : Certifies 649 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0147.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0650 : Certifies 650 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0148.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0651 : Certifies 651 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0149.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0652 : Certifies 652 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0150.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0653 : Certifies 653 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0151.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0654 : Certifies 654 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0152.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0655 : Certifies 655 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0154.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0656 : Certifies 656 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0163.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0657 : Certifies 657 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0169.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0658 : Certifies 658 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0170.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0659 : Certifies 659 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0171.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B021 (j : Fin 30) :
    Certifies (630 + j.val) := by
  fin_cases j
  · exact projection_0630
  · exact projection_0631
  · exact projection_0632
  · exact projection_0633
  · exact projection_0634
  · exact projection_0635
  · exact projection_0636
  · exact projection_0637
  · exact projection_0638
  · exact projection_0639
  · exact projection_0640
  · exact projection_0641
  · exact projection_0642
  · exact projection_0643
  · exact projection_0644
  · exact projection_0645
  · exact projection_0646
  · exact projection_0647
  · exact projection_0648
  · exact projection_0649
  · exact projection_0650
  · exact projection_0651
  · exact projection_0652
  · exact projection_0653
  · exact projection_0654
  · exact projection_0655
  · exact projection_0656
  · exact projection_0657
  · exact projection_0658
  · exact projection_0659

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
