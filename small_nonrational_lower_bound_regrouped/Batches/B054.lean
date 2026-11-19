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
/- Source: ProjectionCertificates/R_one_six_1400.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1400

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 590, 774, 428, 780, 632, 808, 944, 848, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 262, 518, 74, 578, 770, 44, 268, 524, 164, 388, 772, 56, 88, 296, 552, 584, 776, 176, 560, 336, 592, 400, 784, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_774, vertices_428, vertices_780, vertices_632, vertices_808, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_578, vertices_770, vertices_44, vertices_268, vertices_524, vertices_164, vertices_388, vertices_772, vertices_56, vertices_88, vertices_296, vertices_552, vertices_584, vertices_776, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_268), (true, vertices_524), (true, vertices_772), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 1 518 0 268 524 772 296 552 584 776 560 592 784 416 800 391 181 63 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 428
cert_cover_5 2 1 1 2 4 6 44 428 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1400

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1401.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1401

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 590, 646, 898, 684, 376, 616, 944, 864, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 134, 518, 74, 578, 386, 642, 770, 44, 524, 164, 644, 56, 88, 104, 552, 584, 176, 304, 336, 400, 352, 608, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_646, vertices_898, vertices_684, vertices_376, vertices_616, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_134, vertices_518, vertices_74, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_642), (true, vertices_524), (true, vertices_644), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 1 518 0 642 524 644 104 552 584 304 352 608 672 800 896 391 181 63 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1401

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1413.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1413

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 625, 961, 206, 428, 184, 728, 944, 7, 27, 67, 131, 37, 261, 49, 81, 545, 193, 577, 385, 769, 14, 134, 74, 194, 44, 140, 292, 388, 56, 88, 152, 168, 200, 176, 560, 592, 656, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_625, vertices_961, vertices_206, vertices_428, vertices_184, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_292, vertices_388, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_560, vertices_592, vertices_656, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_625), (false, vertices_961), (true, vertices_140), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_416) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

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
cert_coverFacet 1 428
cert_cover_5 1 1 1 2 4 6 44 428 3
cert_coverFacet 2 184
cert_cover_2 2 3 2 4 6 56 184 3
cert_coverFacet 3 728
cert_cover_5 3 2 2 3 5 6 88 728 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1413

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1414.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1414

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 625, 961, 206, 428, 824, 472, 848, 7, 27, 67, 131, 37, 261, 49, 81, 545, 193, 577, 385, 769, 14, 134, 74, 194, 44, 140, 292, 388, 56, 88, 280, 296, 200, 392, 560, 336, 592, 784, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_625, vertices_961, vertices_206, vertices_428, vertices_824, vertices_472, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_292, vertices_388, vertices_56, vertices_88, vertices_280, vertices_296, vertices_200, vertices_392, vertices_560, vertices_336, vertices_592, vertices_784, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_625), (false, vertices_961), (true, vertices_140), (true, vertices_280), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 428
cert_cover_5 1 1 1 2 4 6 44 428 3
cert_coverFacet 2 824
cert_cover_5 2 2 2 3 4 7 56 824 3
cert_coverFacet 3 472
cert_cover_5 3 3 2 3 5 6 88 472 3
cert_coverFacet 4 848
cert_cover_2 4 5 3 7 8 336 848 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1414

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1415.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1415

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 625, 961, 206, 428, 824, 728, 904, 7, 27, 67, 131, 37, 261, 49, 81, 545, 193, 577, 385, 769, 14, 134, 74, 194, 44, 140, 292, 388, 56, 88, 536, 296, 200, 392, 648, 776, 560, 592, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_625, vertices_961, vertices_206, vertices_428, vertices_824, vertices_728, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_292, vertices_388, vertices_56, vertices_88, vertices_536, vertices_296, vertices_200, vertices_392, vertices_648, vertices_776, vertices_560, vertices_592, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_625), (false, vertices_961), (true, vertices_140), (true, vertices_536), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 428
cert_cover_5 1 1 1 2 4 6 44 428 3
cert_coverFacet 2 824
cert_cover_5 2 2 2 3 4 7 56 824 3
cert_coverFacet 3 728
cert_cover_5 3 3 2 3 5 6 88 728 3
cert_coverFacet 4 904
cert_cover_2 4 6 2 7 8 392 904 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1415

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1419.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1419

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 421, 817, 465, 398, 842, 450, 812, 632, 848, 7, 27, 67, 37, 133, 49, 81, 273, 289, 193, 385, 14, 134, 74, 266, 194, 322, 386, 44, 268, 292, 388, 56, 88, 552, 584, 776, 560, 336, 592, 784, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_421, vertices_817, vertices_465, vertices_398, vertices_842, vertices_450, vertices_812, vertices_632, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_560, vertices_336, vertices_592, vertices_784, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_421), (false, vertices_817), (false, vertices_465), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_268), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_592), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_421) then 14 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (false, vertices_465) then 18 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
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
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1419

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1420.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1420

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 142, 458, 428, 312, 856, 992, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 138, 194, 44, 140, 164, 56, 88, 280, 296, 328, 392, 304, 592, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_142, vertices_458, vertices_428, vertices_312, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_392, vertices_304, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_138), (true, vertices_140), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_677) then 14 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
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
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1420

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1421.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1421

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 625, 961, 142, 458, 428, 312, 856, 944, 7, 27, 67, 37, 133, 49, 81, 545, 193, 577, 641, 14, 134, 74, 138, 194, 44, 140, 164, 56, 88, 280, 296, 328, 392, 304, 560, 592, 784, 416, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_625, vertices_961, vertices_142, vertices_458, vertices_428, vertices_312, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_392, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_625), (false, vertices_961), (true, vertices_138), (true, vertices_140), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_304), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_677) then 14 else
  if p.val = (false, vertices_625) then 17 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1421

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1422.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1422

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 549, 901, 817, 465, 654, 458, 556, 376, 936, 7, 27, 67, 37, 133, 517, 49, 81, 273, 545, 193, 385, 769, 14, 134, 74, 138, 194, 44, 524, 548, 644, 56, 88, 296, 552, 328, 392, 648, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_549, vertices_901, vertices_817, vertices_465, vertices_654, vertices_458, vertices_556, vertices_376, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_517, vertices_49, vertices_81, vertices_273, vertices_545, vertices_193, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_549), (false, vertices_901), (false, vertices_817), (false, vertices_465), (true, vertices_138), (true, vertices_524), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_901) then 13 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 936
cert_cover_5 4 3 2 4 6 7 296 936 2
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1422

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1423.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1423

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 451, 805, 369, 897, 206, 684, 184, 472, 944, 7, 27, 67, 131, 37, 517, 49, 81, 289, 321, 385, 641, 769, 14, 134, 74, 194, 44, 140, 548, 644, 56, 88, 152, 168, 200, 176, 304, 336, 400, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_451, vertices_805, vertices_369, vertices_897, vertices_206, vertices_684, vertices_184, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_548, vertices_644, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_451), (false, vertices_805), (false, vertices_369), (false, vertices_897), (true, vertices_140), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 15 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_647) then 9 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_805) then 10 else
  if p.val = (false, vertices_369) then 17 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
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
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

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
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 184
cert_cover_2 2 3 2 4 6 56 184 3
cert_coverFacet 3 472
cert_cover_5 3 2 2 3 5 6 88 472 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1423

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1424.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1424

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 465, 897, 654, 458, 812, 376, 904, 7, 27, 67, 37, 133, 49, 81, 273, 545, 193, 385, 641, 769, 14, 134, 74, 138, 194, 44, 524, 548, 644, 56, 88, 296, 328, 392, 648, 776, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_465, vertices_897, vertices_654, vertices_458, vertices_812, vertices_376, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_273, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_465), (false, vertices_897), (true, vertices_138), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_677) then 13 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 7 376 56 3
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 0 1 2 6 8 654 14 3
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 14 654 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 3 1 2 4 7 44 812 3
cert_coverFacet 3 376
cert_cover_5 3 0 2 3 4 5 56 376 3
cert_coverFacet 4 904
cert_cover_2 4 6 2 7 8 392 904 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1424

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1437.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1437

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 425, 94, 198, 628, 964, 696, 728, 928, 7, 11, 131, 37, 261, 41, 137, 289, 385, 30, 70, 134, 74, 194, 52, 84, 548, 196, 580, 388, 772, 56, 88, 664, 168, 200, 560, 592, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_425, vertices_94, vertices_198, vertices_628, vertices_964, vertices_696, vertices_728, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_289, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_664, vertices_168, vertices_200, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_425), (true, vertices_70), (true, vertices_84), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_664), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_664) then 18 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 628
cert_cover_5 2 2 1 3 4 5 52 628 3
cert_coverFacet 3 964
cert_cover_5 3 3 1 5 6 7 196 964 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 728
cert_cover_5 5 1 2 3 5 6 88 728 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1437

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1438.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1438

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 425, 94, 198, 628, 964, 824, 600, 968, 7, 11, 131, 37, 261, 41, 137, 289, 385, 30, 70, 134, 74, 194, 52, 84, 548, 196, 580, 388, 772, 56, 88, 536, 296, 200, 584, 392, 776, 560, 592, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_425, vertices_94, vertices_198, vertices_628, vertices_964, vertices_824, vertices_600, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_289, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_536, vertices_296, vertices_200, vertices_584, vertices_392, vertices_776, vertices_560, vertices_592, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_425), (true, vertices_70), (true, vertices_84), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_536), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_960) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 5 6 7 8 960
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 628
cert_cover_5 2 2 1 3 4 5 52 628 3
cert_coverFacet 3 964
cert_cover_5 3 1 1 5 6 7 196 964 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 968
cert_cover_5 6 1 2 5 6 7 200 968 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1438

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1439.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1439

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 425, 94, 198, 628, 964, 824, 856, 456, 7, 11, 131, 37, 261, 41, 137, 289, 385, 30, 70, 134, 74, 194, 52, 84, 548, 196, 580, 388, 772, 56, 88, 792, 296, 200, 328, 392, 560, 592, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_425, vertices_94, vertices_198, vertices_628, vertices_964, vertices_824, vertices_856, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_289, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_792, vertices_296, vertices_200, vertices_328, vertices_392, vertices_560, vertices_592, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_425), (true, vertices_70), (true, vertices_84), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_792), (true, vertices_328), (true, vertices_560), (true, vertices_592), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_792) then 18 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 2 3 7 8 792
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 628
cert_cover_5 2 2 1 3 4 5 52 628 3
cert_coverFacet 3 964
cert_cover_5 3 3 1 5 6 7 196 964 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 456
cert_cover_2 6 5 2 6 7 200 456 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1439

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1441.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1441

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 625, 961, 206, 428, 568, 728, 936, 7, 27, 67, 131, 37, 261, 49, 81, 545, 193, 577, 385, 769, 14, 134, 74, 194, 44, 140, 292, 388, 56, 88, 536, 424, 552, 200, 648, 560, 592, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_625, vertices_961, vertices_206, vertices_428, vertices_568, vertices_728, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_292, vertices_388, vertices_56, vertices_88, vertices_536, vertices_424, vertices_552, vertices_200, vertices_648, vertices_560, vertices_592, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_625), (false, vertices_961), (true, vertices_140), (true, vertices_536), (true, vertices_424), (true, vertices_552), (true, vertices_200), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 12 14 16 17 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_391) then 7 else
  if p.val = (false, vertices_91) then 8 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 11 else
  if p.val = (false, vertices_625) then 15 else
  if p.val = (false, vertices_961) then 18 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_424) then 13 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_648) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 7 424
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_rows_3
cert_pivot_3 0 4 2
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 428
cert_cover_5 1 0 1 2 4 6 44 428 3
cert_coverFacet 2 568
cert_cover_2 2 3 2 4 8 56 568 3
cert_coverFacet 3 728
cert_cover_5 3 2 2 3 5 6 88 728 3
cert_coverFacet 4 936
cert_cover_5 4 0 2 4 6 8 424 936 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 3 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1441

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1442.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1442

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 617, 961, 94, 198, 308, 468, 824, 856, 7, 11, 131, 37, 261, 41, 73, 545, 193, 577, 385, 769, 30, 70, 134, 74, 194, 52, 84, 276, 292, 196, 388, 56, 88, 792, 552, 584, 304, 336, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_617, vertices_961, vertices_94, vertices_198, vertices_308, vertices_468, vertices_824, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_73, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_276, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_792, vertices_552, vertices_584, vertices_304, vertices_336, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_617), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_88), (true, vertices_792), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 13 16 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_391) then 8 else
  if p.val = (false, vertices_203) then 9 else
  if p.val = (false, vertices_805) then 12 else
  if p.val = (false, vertices_617) then 14 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_792) then 15 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 2 3 7 8 792
cert_row_4 2 1 3 5 6 7 468 84 3
cert_rows_3
cert_pivot_3 2 0 1
cert_heightProof 3
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 308
cert_cover_2 2 3 1 4 7 52 308 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1442

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1443.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1443

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 617, 961, 94, 198, 820, 468, 568, 856, 7, 11, 131, 37, 261, 41, 73, 545, 193, 577, 385, 769, 30, 70, 134, 74, 194, 52, 84, 276, 804, 196, 388, 56, 88, 536, 552, 584, 560, 336, 784, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_617, vertices_961, vertices_94, vertices_198, vertices_820, vertices_468, vertices_568, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_73, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_276, vertices_804, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_560, vertices_336, vertices_784, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_617), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_88), (true, vertices_536), (true, vertices_560), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 1 4 7 8 804
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 52 820 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1443

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1447.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1447

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 323, 677, 809, 961, 94, 842, 244, 696, 728, 7, 11, 67, 259, 37, 133, 41, 265, 545, 193, 321, 641, 769, 30, 70, 74, 266, 322, 52, 84, 164, 196, 56, 88, 664, 552, 584, 776, 176, 208, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_323, vertices_677, vertices_809, vertices_961, vertices_94, vertices_842, vertices_244, vertices_696, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_37, vertices_133, vertices_41, vertices_265, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_266, vertices_322, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_664, vertices_552, vertices_584, vertices_776, vertices_176, vertices_208, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_323), (false, vertices_677), (false, vertices_809), (false, vertices_961), (true, vertices_74), (true, vertices_84), (true, vertices_88), (true, vertices_664), (true, vertices_584), (true, vertices_176), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 13 16 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_677) then 12 else
  if p.val = (false, vertices_809) then 14 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_664) then 15 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
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
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 244
cert_cover_5 2 3 1 3 4 5 52 244 3
cert_coverFacet 3 696
cert_cover_5 3 1 2 3 4 6 56 696 3
cert_coverFacet 4 728
cert_cover_5 4 1 2 3 5 6 88 728 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1447

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1470.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1470

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 422, 810, 820, 852, 452, 632, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 266, 290, 386, 52, 84, 788, 292, 196, 324, 388, 56, 88, 552, 584, 776, 560, 592, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_422, vertices_810, vertices_820, vertices_852, vertices_452, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_290, vertices_386, vertices_52, vertices_84, vertices_788, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_560, vertices_592, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_290), (true, vertices_788), (true, vertices_292), (true, vertices_324), (true, vertices_388), (true, vertices_552), (true, vertices_560), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 16 12 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_395) then 11 else
  if p.val = (false, vertices_93) then 14 else
  if p.val = (false, vertices_841) then 15 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_788) then 17 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 38 3
cert_row_2 1 1 3 7 8 788
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 38 422 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 52 820 3
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 7 84 852 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1470

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1475.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1475

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 451, 165, 369, 929, 206, 684, 824, 728, 976, 7, 27, 67, 131, 37, 133, 49, 81, 161, 289, 321, 385, 14, 134, 74, 194, 44, 140, 164, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_451, vertices_165, vertices_369, vertices_929, vertices_206, vertices_684, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_451), (false, vertices_165), (false, vertices_369), (false, vertices_929), (true, vertices_140), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_720), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 13 14 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 9 else
  if p.val = (false, vertices_451) then 10 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_369) then 15 else
  if p.val = (false, vertices_929) then 18 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_720) then 16 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1475

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1476.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1476

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 625, 961, 142, 458, 172, 440, 856, 944, 7, 27, 67, 37, 133, 49, 81, 545, 193, 577, 641, 14, 134, 74, 138, 194, 44, 140, 164, 56, 88, 280, 168, 328, 392, 432, 560, 592, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_625, vertices_961, vertices_142, vertices_458, vertices_172, vertices_440, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_280, vertices_168, vertices_328, vertices_392, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_625), (false, vertices_961), (true, vertices_138), (true, vertices_140), (true, vertices_280), (true, vertices_168), (true, vertices_328), (true, vertices_392), (true, vertices_432), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 13 14 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 8 else
  if p.val = (false, vertices_91) then 9 else
  if p.val = (false, vertices_677) then 12 else
  if p.val = (false, vertices_625) then 15 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_432) then 16 else
  if p.val = (true, vertices_784) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_rows_3
cert_pivot_3 0 4 2
cert_heightProof 3
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 440
cert_cover_5 3 0 2 3 4 6 56 440 3
cert_coverFacet 4 856
cert_cover_5 4 2 2 3 5 7 88 856 3
cert_coverFacet 5 944
cert_cover_5 5 0 3 4 6 8 432 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1476

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1477.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1477

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 561, 721, 142, 458, 428, 824, 856, 992, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 138, 194, 44, 140, 164, 56, 88, 792, 296, 328, 392, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_561, vertices_721, vertices_142, vertices_458, vertices_428, vertices_824, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_792, vertices_296, vertices_328, vertices_392, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_561), (false, vertices_721), (true, vertices_138), (true, vertices_140), (true, vertices_792), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_792) then 17 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 7 8 792
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 3 0 1 4
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 824
cert_cover_5 3 0 2 3 4 7 56 824 3
cert_coverFacet 4 856
cert_cover_5 4 0 2 3 5 7 88 856 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1477

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1478.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1478

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 142, 458, 428, 376, 976, 928, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 138, 194, 44, 140, 164, 56, 88, 296, 328, 392, 304, 720, 336, 784, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_142, vertices_458, vertices_428, vertices_376, vertices_976, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_304, vertices_720, vertices_336, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_138), (true, vertices_140), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_677) then 14 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
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
cert_row_2 0 3 5 6 8 720
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 376
cert_cover_5 3 3 2 3 4 5 56 376 3
cert_coverFacet 4 976
cert_cover_5 4 0 3 5 6 7 720 976 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1478

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1479.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1479

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 625, 961, 142, 458, 428, 824, 856, 928, 7, 27, 67, 37, 133, 49, 81, 545, 193, 577, 641, 14, 134, 74, 138, 194, 44, 140, 164, 56, 88, 792, 296, 328, 392, 560, 592, 416, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_625, vertices_961, vertices_142, vertices_458, vertices_428, vertices_824, vertices_856, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_792, vertices_296, vertices_328, vertices_392, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_625), (false, vertices_961), (true, vertices_138), (true, vertices_140), (true, vertices_792), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 13 15 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 8 else
  if p.val = (false, vertices_91) then 9 else
  if p.val = (false, vertices_677) then 12 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_792) then 14 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_800) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 7 8 792
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 1 2 4 6 7 428 44 3
cert_rows_3
cert_pivot_3 0 3 1
cert_heightProof 3
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 824
cert_cover_5 3 0 2 3 4 7 56 824 3
cert_coverFacet 4 856
cert_cover_5 4 0 2 3 5 7 88 856 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1479

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1480.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1480

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 561, 849, 961, 142, 458, 428, 376, 944, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 833, 641, 14, 134, 74, 138, 194, 44, 140, 164, 56, 88, 296, 328, 392, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_561, vertices_849, vertices_961, vertices_142, vertices_458, vertices_428, vertices_376, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_833, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_561), (false, vertices_849), (false, vertices_961), (true, vertices_138), (true, vertices_140), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 16 17 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_677) then 13 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_416) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 428
cert_cover_5 2 1 1 2 4 6 44 428 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 304 944 2
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1480

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1482.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1482

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 805, 389, 625, 961, 142, 458, 428, 824, 856, 7, 27, 67, 37, 133, 261, 49, 81, 545, 193, 577, 385, 769, 14, 134, 74, 138, 194, 44, 140, 292, 388, 56, 88, 792, 296, 328, 392, 560, 592, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_805, vertices_389, vertices_625, vertices_961, vertices_142, vertices_458, vertices_428, vertices_824, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_261, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_292, vertices_388, vertices_56, vertices_88, vertices_792, vertices_296, vertices_328, vertices_392, vertices_560, vertices_592, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_805), (false, vertices_389), (false, vertices_625), (false, vertices_961), (true, vertices_138), (true, vertices_140), (true, vertices_792), (true, vertices_296), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 12 14 16 17 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 7 else
  if p.val = (false, vertices_91) then 8 else
  if p.val = (false, vertices_805) then 11 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_625) then 15 else
  if p.val = (false, vertices_961) then 18 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_792) then 13 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 7 8 792
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 1 2 4 6 7 428 44 3
cert_rows_3
cert_pivot_3 0 3 1
cert_heightProof 3
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 824
cert_cover_5 3 0 2 3 4 7 56 824 3
cert_coverFacet 4 856
cert_cover_5 4 0 2 3 5 7 88 856 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 3 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1482

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1483.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1483

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 549, 901, 817, 465, 142, 458, 684, 376, 936, 7, 27, 67, 37, 133, 517, 49, 81, 273, 545, 193, 385, 769, 14, 134, 74, 138, 194, 44, 140, 548, 644, 56, 88, 680, 296, 328, 392, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_549, vertices_901, vertices_817, vertices_465, vertices_142, vertices_458, vertices_684, vertices_376, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_517, vertices_49, vertices_81, vertices_273, vertices_545, vertices_193, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_548, vertices_644, vertices_56, vertices_88, vertices_680, vertices_296, vertices_328, vertices_392, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_549), (false, vertices_901), (false, vertices_817), (false, vertices_465), (true, vertices_138), (true, vertices_140), (true, vertices_680), (true, vertices_296), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 12 14 17 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 7 else
  if p.val = (false, vertices_91) then 8 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_901) then 11 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (false, vertices_465) then 16 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_680) then 13 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 8 680
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_rows_3
cert_pivot_3 0 8 2
cert_heightProof 3
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 936
cert_cover_5 4 0 2 4 6 7 680 936 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 3 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1483

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1485.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1485

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 465, 897, 142, 458, 812, 908, 376, 7, 27, 67, 37, 133, 49, 81, 273, 545, 193, 385, 641, 769, 14, 134, 74, 138, 194, 44, 140, 780, 548, 644, 56, 88, 296, 328, 392, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_465, vertices_897, vertices_142, vertices_458, vertices_812, vertices_908, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_273, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_780, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_465), (false, vertices_897), (true, vertices_138), (true, vertices_140), (true, vertices_780), (true, vertices_296), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 13 14 17 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 7 else
  if p.val = (false, vertices_91) then 8 else
  if p.val = (false, vertices_677) then 11 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (false, vertices_465) then 16 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_780) then 12 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_392) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 908
cert_cover_5 3 0 1 2 6 7 140 908 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 3 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1485

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1487.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1487

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 810, 436, 468, 376, 904, 928, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 546, 642, 52, 84, 404, 164, 196, 56, 88, 296, 328, 392, 648, 776, 304, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_810, vertices_436, vertices_468, vertices_376, vertices_904, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_404, vertices_164, vertices_196, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_404), (true, vertices_164), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 17 13 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_457) then 16 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_404) then 18 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
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
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 52 436 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 376
cert_cover_5 4 0 2 3 4 5 56 376 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1487

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1493.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1493

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 421, 625, 225, 398, 458, 812, 568, 856, 992, 7, 27, 67, 37, 133, 49, 81, 97, 161, 193, 14, 134, 74, 394, 194, 44, 268, 292, 388, 56, 88, 536, 552, 328, 776, 560, 592, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_421, vertices_625, vertices_225, vertices_398, vertices_458, vertices_812, vertices_568, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_97, vertices_161, vertices_193, vertices_14, vertices_134, vertices_74, vertices_394, vertices_194, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_592, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_421), (false, vertices_625), (false, vertices_225), (true, vertices_394), (true, vertices_268), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 9 18 12 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_421) then 11 else
  if p.val = (false, vertices_625) then 15 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_394) then 17 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 856
cert_cover_5 4 2 2 3 5 7 88 856 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1493

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1620 : Certifies 1620 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1400.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1621 : Certifies 1621 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1401.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1622 : Certifies 1622 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1413.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1623 : Certifies 1623 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1414.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1624 : Certifies 1624 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1415.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1625 : Certifies 1625 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1419.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1626 : Certifies 1626 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1420.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1627 : Certifies 1627 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1421.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1628 : Certifies 1628 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1422.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1629 : Certifies 1629 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1423.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1630 : Certifies 1630 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1424.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1631 : Certifies 1631 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1437.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1632 : Certifies 1632 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1438.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1633 : Certifies 1633 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1439.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1634 : Certifies 1634 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1441.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1635 : Certifies 1635 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1442.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1636 : Certifies 1636 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1443.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1637 : Certifies 1637 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1447.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1638 : Certifies 1638 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1470.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1639 : Certifies 1639 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1475.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1640 : Certifies 1640 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1476.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1641 : Certifies 1641 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1477.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1642 : Certifies 1642 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1478.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1643 : Certifies 1643 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1479.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1644 : Certifies 1644 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1480.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1645 : Certifies 1645 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1482.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1646 : Certifies 1646 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1483.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1647 : Certifies 1647 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1485.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1648 : Certifies 1648 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1487.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1649 : Certifies 1649 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1493.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B054 (j : Fin 30) :
    Certifies (1620 + j.val) := by
  fin_cases j
  · exact projection_1620
  · exact projection_1621
  · exact projection_1622
  · exact projection_1623
  · exact projection_1624
  · exact projection_1625
  · exact projection_1626
  · exact projection_1627
  · exact projection_1628
  · exact projection_1629
  · exact projection_1630
  · exact projection_1631
  · exact projection_1632
  · exact projection_1633
  · exact projection_1634
  · exact projection_1635
  · exact projection_1636
  · exact projection_1637
  · exact projection_1638
  · exact projection_1639
  · exact projection_1640
  · exact projection_1641
  · exact projection_1642
  · exact projection_1643
  · exact projection_1644
  · exact projection_1645
  · exact projection_1646
  · exact projection_1647
  · exact projection_1648
  · exact projection_1649

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
