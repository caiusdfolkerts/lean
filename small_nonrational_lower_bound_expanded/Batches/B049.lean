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
/- Source: ProjectionCertificates/R_one_six_1275.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1275

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 206, 706, 428, 376, 968, 432, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 134, 74, 194, 578, 642, 44, 140, 164, 56, 88, 296, 200, 328, 392, 176, 304, 336, 400, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_206, vertices_706, vertices_428, vertices_376, vertices_968, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_578, vertices_642, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_194), (true, vertices_140), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_304), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 337 1 194 140 296 200 328 392 304 416 704 647 181 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 428
cert_cover_5 2 1 1 2 4 6 44 428 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 968
cert_cover_5 4 3 2 5 6 7 200 968 3
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1275

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1276.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1276

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 142, 714, 236, 376, 432, 992, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 134, 74, 138, 578, 642, 44, 140, 164, 56, 88, 104, 200, 176, 304, 336, 400, 224, 352, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_142, vertices_714, vertices_236, vertices_376, vertices_432, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_578, vertices_642, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_104, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_138), (true, vertices_140), (true, vertices_104), (true, vertices_200), (true, vertices_304), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 337 1 138 140 104 200 304 224 352 416 704 647 181 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 236
cert_cover_5 2 1 1 2 4 5 44 236 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 432
cert_cover_2 4 4 3 6 7 176 432 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1276

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1277.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1277

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 181, 361, 929, 94, 838, 330, 340, 916, 120, 496, 7, 11, 515, 53, 133, 41, 265, 161, 289, 641, 769, 30, 70, 518, 74, 266, 322, 770, 84, 148, 276, 324, 644, 772, 56, 88, 104, 328, 112, 176, 336, 400, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_181, vertices_361, vertices_929, vertices_94, vertices_838, vertices_330, vertices_340, vertices_916, vertices_120, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_265, vertices_161, vertices_289, vertices_641, vertices_769, vertices_30, vertices_70, vertices_518, vertices_74, vertices_266, vertices_322, vertices_770, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_328, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_181), (false, vertices_361), (false, vertices_929), (true, vertices_70), (true, vertices_74), (true, vertices_322), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_112), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_400) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 340
cert_cover_2 3 3 1 5 7 84 340 3
cert_coverFacet 4 916
cert_cover_5 4 2 1 3 6 7 148 916 3
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1277

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1278.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1278

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 369, 961, 654, 202, 706, 188, 676, 472, 944, 7, 27, 67, 37, 517, 49, 81, 289, 321, 577, 769, 14, 518, 74, 138, 194, 578, 642, 60, 140, 164, 548, 644, 88, 152, 200, 176, 304, 336, 400, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_369, vertices_961, vertices_654, vertices_202, vertices_706, vertices_188, vertices_676, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_138, vertices_194, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_369), (false, vertices_961), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 188
cert_cover_5 3 1 1 2 3 6 60 188 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1278

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1279.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1279

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 654, 202, 706, 188, 676, 472, 992, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 518, 74, 138, 194, 578, 642, 60, 140, 164, 548, 644, 88, 152, 200, 176, 336, 400, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_654, vertices_202, vertices_706, vertices_188, vertices_676, vertices_472, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_138, vertices_194, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
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
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 194 642 140 164 644 152 200 672 448 704 583 91 63 805 433 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 188
cert_cover_5 3 1 1 2 3 6 60 188 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1279

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1280.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1280

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 654, 202, 962, 188, 676, 472, 928, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 518, 74, 138, 194, 578, 642, 60, 140, 164, 548, 644, 88, 152, 200, 176, 336, 400, 416, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_654, vertices_202, vertices_962, vertices_188, vertices_676, vertices_472, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_138, vertices_194, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
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
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 194 642 140 164 644 152 200 672 448 896 583 91 63 805 433 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 194 962 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 6 60 188 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 88 472 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1280

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1281.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1281

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 654, 598, 202, 962, 820, 676, 848, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 138, 82, 194, 578, 642, 140, 52, 532, 164, 548, 644, 200, 304, 336, 592, 784, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_598, vertices_202, vertices_962, vertices_820, vertices_676, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_532, vertices_164, vertices_548, vertices_644, vertices_200, vertices_304, vertices_336, vertices_592, vertices_784, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_592), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 518 138 194 578 642 532 548 644 592 784 832
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 598
cert_cover_5 1 2 0 1 3 5 22 598 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1281

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1282.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1282

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 654, 202, 962, 188, 420, 900, 472, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 518, 74, 138, 194, 578, 642, 60, 140, 164, 292, 388, 644, 772, 88, 152, 200, 176, 336, 400, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_654, vertices_202, vertices_962, vertices_188, vertices_420, vertices_900, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_138, vertices_194, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_200, vertices_176, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
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
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 194 642 140 164 388 644 152 200 448 896 583 91 63 805 433 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 194 962 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 6 60 188 3
cert_coverFacet 4 420
cert_cover_2 4 4 1 6 7 164 420 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1282

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1283.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1283

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 654, 598, 202, 962, 692, 816, 848, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 138, 82, 194, 578, 642, 140, 52, 532, 164, 644, 200, 304, 560, 336, 592, 784, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_598, vertices_202, vertices_962, vertices_692, vertices_816, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 518 138 194 578 642 532 644 560 592 784 832
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 598
cert_cover_5 1 2 0 1 3 5 22 598 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 692
cert_cover_5 4 3 1 3 4 6 52 692 3
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1283

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1284.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1284

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 654, 598, 202, 962, 692, 624, 864, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 138, 82, 194, 578, 642, 140, 52, 532, 164, 644, 200, 112, 560, 592, 352, 608, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_598, vertices_202, vertices_962, vertices_692, vertices_624, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_112, vertices_560, vertices_592, vertices_352, vertices_608, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 518 138 194 578 642 532 644 560 592 608 832
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 598
cert_cover_5 1 2 0 1 3 5 22 598 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 692
cert_cover_5 4 3 1 3 4 6 52 692 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1284

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1285.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1285

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 139, 899, 109, 597, 425, 865, 126, 662, 186, 240, 976, 480, 11, 131, 515, 13, 69, 517, 41, 137, 97, 289, 577, 385, 769, 14, 22, 518, 58, 138, 146, 642, 108, 84, 532, 168, 112, 176, 208, 592, 656, 224, 352, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_139, vertices_899, vertices_109, vertices_597, vertices_425, vertices_865, vertices_126, vertices_662, vertices_186, vertices_240, vertices_976, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_515, vertices_13, vertices_69, vertices_517, vertices_41, vertices_137, vertices_97, vertices_289, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_518, vertices_58, vertices_138, vertices_146, vertices_642, vertices_108, vertices_84, vertices_532, vertices_168, vertices_112, vertices_176, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_139), (false, vertices_899), (false, vertices_109), (false, vertices_597), (false, vertices_425), (false, vertices_865), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 10 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_899) then 11 else
  if p.val = (false, vertices_109) then 14 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_865) then 20 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_58) then 12 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_112) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 14 3
cert_row_4 1 0 1 2 3 5 126 14 3
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 4 2 0 3
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 186
cert_cover 2 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 3 240
cert_cover_2 3 4 3 5 6 112 240 3
cert_coverFacet 4 976
cert_cover_5 4 3 3 5 6 7 208 976 3
cert_coverFacet 5 480
cert_cover_2 5 5 4 6 7 224 480 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1285

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1286.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1286

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 139, 899, 109, 597, 425, 865, 126, 662, 186, 368, 432, 976, 11, 131, 515, 13, 69, 517, 41, 137, 97, 289, 577, 385, 769, 14, 22, 518, 58, 138, 146, 642, 108, 84, 532, 168, 112, 176, 304, 336, 592, 400, 656, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_139, vertices_899, vertices_109, vertices_597, vertices_425, vertices_865, vertices_126, vertices_662, vertices_186, vertices_368, vertices_432, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_515, vertices_13, vertices_69, vertices_517, vertices_41, vertices_137, vertices_97, vertices_289, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_518, vertices_58, vertices_138, vertices_146, vertices_642, vertices_108, vertices_84, vertices_532, vertices_168, vertices_112, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_656, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_139), (false, vertices_899), (false, vertices_109), (false, vertices_597), (false, vertices_425), (false, vertices_865), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 10 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_899) then 11 else
  if p.val = (false, vertices_109) then 14 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_865) then 20 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_58) then 12 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_112) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 14 3
cert_row_4 1 0 1 2 3 5 126 14 3
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 4 2 0 3
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 186
cert_cover 2 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 3 368
cert_cover_2 3 4 3 5 7 112 368 3
cert_coverFacet 4 432
cert_cover_2 4 4 3 6 7 176 432 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 336 976 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1286

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1287.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1287

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 139, 899, 109, 837, 425, 369, 126, 662, 186, 596, 432, 976, 11, 131, 515, 13, 69, 517, 41, 137, 97, 289, 321, 385, 769, 14, 22, 518, 58, 138, 146, 642, 108, 84, 532, 580, 168, 112, 176, 304, 336, 592, 400, 656, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_139, vertices_899, vertices_109, vertices_837, vertices_425, vertices_369, vertices_126, vertices_662, vertices_186, vertices_596, vertices_432, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_515, vertices_13, vertices_69, vertices_517, vertices_41, vertices_137, vertices_97, vertices_289, vertices_321, vertices_385, vertices_769, vertices_14, vertices_22, vertices_518, vertices_58, vertices_138, vertices_146, vertices_642, vertices_108, vertices_84, vertices_532, vertices_580, vertices_168, vertices_112, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_656, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_139), (false, vertices_899), (false, vertices_109), (false, vertices_837), (false, vertices_425), (false, vertices_369), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_84), (true, vertices_532), (true, vertices_176), (true, vertices_592), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 10 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_899) then 11 else
  if p.val = (false, vertices_109) then 14 else
  if p.val = (false, vertices_837) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_58) then 12 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 14 3
cert_row_4 1 0 1 2 3 5 126 14 3
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 4 2 0 3
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 186
cert_cover 2 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 3 596
cert_cover_2 3 3 1 5 8 84 596 3
cert_coverFacet 4 432
cert_cover_2 4 4 3 6 7 176 432 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 336 976 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1287

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1288.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1288

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 433, 849, 654, 598, 202, 962, 564, 932, 816, 27, 45, 73, 137, 49, 81, 273, 161, 321, 385, 14, 22, 518, 74, 138, 82, 194, 578, 642, 140, 52, 532, 164, 548, 644, 200, 304, 560, 592, 784, 416, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_433, vertices_849, vertices_654, vertices_598, vertices_202, vertices_962, vertices_564, vertices_932, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_273, vertices_161, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_532, vertices_164, vertices_548, vertices_644, vertices_200, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_433), (false, vertices_849), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_560), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 194 962 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 932
cert_cover_5 5 3 1 4 6 7 164 932 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1288

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1289.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1289

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 433, 849, 654, 598, 202, 962, 308, 788, 932, 27, 45, 73, 137, 49, 81, 273, 161, 321, 385, 14, 22, 518, 74, 138, 82, 194, 578, 642, 140, 52, 276, 532, 164, 292, 644, 772, 200, 304, 592, 784, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_433, vertices_849, vertices_654, vertices_598, vertices_202, vertices_962, vertices_308, vertices_788, vertices_932] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_273, vertices_161, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_644, vertices_772, vertices_200, vertices_304, vertices_592, vertices_784, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_433), (false, vertices_849), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_644), (true, vertices_772), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 194 962 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 932
cert_cover_5 6 3 1 4 6 7 164 932 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1289

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1290.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1290

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 654, 598, 202, 962, 116, 868, 676, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 138, 82, 194, 578, 642, 140, 52, 84, 100, 164, 548, 580, 644, 200, 112, 352, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_598, vertices_202, vertices_962, vertices_116, vertices_868, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_84, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_200, vertices_112, vertices_352, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_84), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 518 138 194 578 642 84 100 548 580 644 832
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 194 962 3
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 868
cert_cover_5 5 3 1 4 5 7 100 868 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1290

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1291.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1291

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 361, 929, 833, 94, 198, 962, 468, 440, 344, 7, 11, 515, 53, 133, 41, 73, 161, 289, 321, 577, 641, 769, 30, 70, 134, 74, 194, 578, 642, 84, 148, 196, 56, 88, 280, 296, 328, 176, 336, 400, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_929, vertices_833, vertices_94, vertices_198, vertices_962, vertices_468, vertices_440, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_578, vertices_642, vertices_84, vertices_148, vertices_196, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_929), (false, vertices_833), (true, vertices_70), (true, vertices_194), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_280), (true, vertices_336), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 440
cert_cover_5 4 3 2 3 4 6 56 440 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1291

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1292.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1292

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 654, 342, 774, 202, 962, 820, 676, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 262, 518, 74, 138, 82, 194, 322, 642, 770, 140, 52, 276, 164, 548, 644, 772, 200, 304, 336, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_342, vertices_774, vertices_202, vertices_962, vertices_820, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_322, vertices_642, vertices_770, vertices_140, vertices_52, vertices_276, vertices_164, vertices_548, vertices_644, vertices_772, vertices_200, vertices_304, vertices_336, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_276), (true, vertices_548), (true, vertices_644), (true, vertices_772)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 262 518 138 194 322 642 770 276 548 644 772
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 3 5 7 342 22 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 342
cert_cover_5 1 2 0 1 3 5 22 342 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 194 962 3
cert_coverFacet 5 820
cert_cover_5 5 3 1 3 4 7 52 820 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1292

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1293.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1293

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 654, 790, 202, 338, 962, 692, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 138, 82, 274, 194, 322, 642, 770, 140, 52, 532, 164, 644, 200, 304, 560, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_790, vertices_202, vertices_338, vertices_962, vertices_692, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_138, vertices_82, vertices_274, vertices_194, vertices_322, vertices_642, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_138), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 518 138 274 194 322 642 770 532 644 560 784
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 194 962 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1293

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1294.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1294

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 165, 369, 929, 590, 188, 204, 964, 472, 432, 7, 27, 67, 515, 37, 133, 49, 81, 161, 289, 321, 641, 769, 14, 518, 74, 578, 60, 76, 140, 164, 196, 580, 644, 88, 152, 200, 176, 304, 336, 400, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_165, vertices_369, vertices_929, vertices_590, vertices_188, vertices_204, vertices_964, vertices_472, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_133, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_60, vertices_76, vertices_140, vertices_164, vertices_196, vertices_580, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_165), (false, vertices_369), (false, vertices_929), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_580), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 10 16 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_369) then 18 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 2 5 8 590 14 3
cert_row_4 2 1 5 6 7 8 964 196 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 14 590 3
cert_coverFacet 1 188
cert_cover_5 1 0 1 2 3 6 60 188 3
cert_coverFacet 2 204
cert_cover_2 2 2 1 5 6 76 204 3
cert_coverFacet 3 964
cert_cover_5 3 2 1 5 6 7 196 964 3
cert_coverFacet 4 472
cert_cover_5 4 3 2 3 5 6 88 472 3
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1294

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1295.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1295

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 590, 534, 850, 204, 692, 964, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 82, 530, 578, 76, 140, 52, 532, 164, 196, 580, 644, 200, 304, 560, 336, 784, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_590, vertices_534, vertices_850, vertices_204, vertices_692, vertices_964, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_82, vertices_530, vertices_578, vertices_76, vertices_140, vertices_52, vertices_532, vertices_164, vertices_196, vertices_580, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_530), (true, vertices_578), (true, vertices_76), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_560), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 518 530 578 76 532 196 580 644 560 784 832
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 82 850 3
cert_coverFacet 3 204
cert_cover_2 3 2 1 5 6 76 204 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 964
cert_cover_5 5 3 1 5 6 7 196 964 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1295

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1296.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1296

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 369, 961, 654, 586, 188, 676, 472, 712, 944, 7, 27, 67, 37, 517, 49, 81, 289, 321, 577, 769, 14, 518, 74, 522, 578, 60, 140, 164, 548, 644, 88, 152, 200, 584, 648, 176, 304, 336, 400, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_369, vertices_961, vertices_654, vertices_586, vertices_188, vertices_676, vertices_472, vertices_712, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_522, vertices_578, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_369), (false, vertices_961), (true, vertices_522), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 188
cert_cover_5 2 1 1 2 3 6 60 188 3
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 472
cert_cover_5 4 2 2 3 5 6 88 472 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1296

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1297.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1297

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 654, 586, 188, 676, 472, 712, 992, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 518, 74, 522, 578, 60, 140, 164, 548, 644, 88, 152, 200, 584, 648, 176, 336, 400, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_654, vertices_586, vertices_188, vertices_676, vertices_472, vertices_712, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_522, vertices_578, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_584, vertices_648, vertices_176, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_522), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 522 140 164 644 152 200 584 648 672 448 704 583 91 63 805 433 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 188
cert_cover_5 2 1 1 2 3 6 60 188 3
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 472
cert_cover_5 4 2 2 3 5 6 88 472 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1297

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1298.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1298

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 181, 681, 961, 94, 330, 468, 376, 808, 944, 7, 11, 67, 259, 53, 133, 41, 521, 161, 193, 321, 641, 769, 30, 70, 74, 266, 322, 84, 148, 196, 56, 88, 296, 552, 328, 776, 176, 304, 336, 400, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_181, vertices_681, vertices_961, vertices_94, vertices_330, vertices_468, vertices_376, vertices_808, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_53, vertices_133, vertices_41, vertices_521, vertices_161, vertices_193, vertices_321, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_266, vertices_322, vertices_84, vertices_148, vertices_196, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_181), (false, vertices_681), (false, vertices_961), (true, vertices_74), (true, vertices_84), (true, vertices_88), (true, vertices_296), (true, vertices_328), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 468
cert_cover_5 2 1 1 3 5 6 84 468 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 808
cert_cover_2 4 4 2 7 8 296 808 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1298

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1299.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1299

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 206, 534, 582, 850, 692, 964, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 70, 518, 74, 82, 530, 578, 140, 52, 532, 164, 196, 580, 644, 200, 304, 560, 336, 784, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_206, vertices_534, vertices_582, vertices_850, vertices_692, vertices_964, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_82, vertices_530, vertices_578, vertices_140, vertices_52, vertices_532, vertices_164, vertices_196, vertices_580, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_70), (true, vertices_518), (true, vertices_530), (true, vertices_578), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_560), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 70 518 530 578 532 196 580 644 560 784 832
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 850
cert_cover_5 3 1 0 3 5 7 82 850 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 964
cert_cover_5 5 3 1 5 6 7 196 964 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1299

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1300.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1300

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 677, 625, 897, 206, 450, 188, 472, 944, 848, 7, 27, 67, 259, 37, 133, 49, 81, 545, 577, 385, 641, 769, 14, 134, 74, 194, 322, 386, 60, 140, 164, 88, 152, 200, 176, 560, 336, 592, 400, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_677, vertices_625, vertices_897, vertices_206, vertices_450, vertices_188, vertices_472, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_60, vertices_140, vertices_164, vertices_88, vertices_152, vertices_200, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_677), (false, vertices_625), (false, vertices_897), (true, vertices_194), (true, vertices_140), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_677) then 12 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 897 1 194 140 152 200 176 336 400 784 448 391 677 91 835 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 188
cert_cover_5 2 1 1 2 3 6 60 188 3
cert_coverFacet 3 472
cert_cover_5 3 2 2 3 5 6 88 472 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1300

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1301.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1301

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 805, 625, 206, 450, 188, 420, 472, 944, 848, 7, 27, 67, 259, 37, 261, 49, 81, 545, 577, 769, 14, 134, 74, 194, 322, 386, 60, 140, 164, 292, 388, 88, 152, 200, 176, 560, 336, 592, 400, 784, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_805, vertices_625, vertices_206, vertices_450, vertices_188, vertices_420, vertices_472, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_577, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_60, vertices_140, vertices_164, vertices_292, vertices_388, vertices_88, vertices_152, vertices_200, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_625), (true, vertices_194), (true, vertices_140), (true, vertices_164), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
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
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 194 1 140 164 152 200 176 336 400 784 416 448 391 805 91 835 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 188
cert_cover_5 2 1 1 2 3 6 60 188 3
cert_coverFacet 3 420
cert_cover_2 3 4 1 6 7 164 420 3
cert_coverFacet 4 472
cert_cover_5 4 2 2 3 5 6 88 472 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1301

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1302.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1302

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 625, 929, 833, 206, 534, 902, 850, 450, 692, 27, 45, 73, 137, 49, 81, 161, 545, 321, 577, 385, 769, 14, 22, 134, 518, 74, 82, 530, 194, 322, 386, 770, 140, 52, 532, 164, 644, 200, 560, 592, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_625, vertices_929, vertices_833, vertices_206, vertices_534, vertices_902, vertices_850, vertices_450, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_134, vertices_518, vertices_74, vertices_82, vertices_530, vertices_194, vertices_322, vertices_386, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_560, vertices_592, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_625), (false, vertices_929), (false, vertices_833), (true, vertices_134), (true, vertices_518), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_644)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_173) then 14 else
  if p.val = (false, vertices_457) then 16 else
  if p.val = (false, vertices_625) then 18 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 134 902 3
cert_coverFacet 3 850
cert_cover_5 3 1 0 3 5 7 82 850 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1302

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1303.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1303

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 206, 534, 902, 850, 450, 692, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 134, 518, 74, 82, 530, 194, 322, 386, 770, 140, 52, 532, 164, 644, 200, 304, 560, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_206, vertices_534, vertices_902, vertices_850, vertices_450, vertices_692, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_134, vertices_518, vertices_74, vertices_82, vertices_530, vertices_194, vertices_322, vertices_386, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_134), (true, vertices_518), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
cert_nodeAtPriority_16 134 518 530 194 322 386 770 532 644 560 784
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 134 902 3
cert_coverFacet 3 850
cert_cover_5 3 1 0 3 5 7 82 850 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1303

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1304.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1304

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 805, 369, 206, 450, 898, 188, 676, 472, 944, 7, 27, 67, 515, 37, 517, 49, 81, 289, 321, 769, 14, 134, 74, 194, 322, 386, 642, 770, 60, 140, 164, 548, 644, 88, 152, 200, 176, 304, 336, 400, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_805, vertices_369, vertices_206, vertices_450, vertices_898, vertices_188, vertices_676, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_369), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_164), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
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
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_58 0 194 1 386 140 164 152 200 176 400 672 448 896 647 805 91 835 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 2 3 4 60
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
cert_coverFacet 3 188
cert_cover_5 3 1 1 2 3 6 60 188 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1304

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1470 : Certifies 1470 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1275.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1471 : Certifies 1471 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1276.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1472 : Certifies 1472 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1277.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1473 : Certifies 1473 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1278.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1474 : Certifies 1474 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1279.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1475 : Certifies 1475 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1280.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1476 : Certifies 1476 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1281.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1477 : Certifies 1477 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1282.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1478 : Certifies 1478 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1283.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1479 : Certifies 1479 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1284.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1480 : Certifies 1480 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1285.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1481 : Certifies 1481 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1286.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1482 : Certifies 1482 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1287.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1483 : Certifies 1483 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1288.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1484 : Certifies 1484 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1289.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1485 : Certifies 1485 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1290.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1486 : Certifies 1486 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1291.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1487 : Certifies 1487 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1292.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1488 : Certifies 1488 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1293.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1489 : Certifies 1489 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1294.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1490 : Certifies 1490 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1295.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1491 : Certifies 1491 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1296.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1492 : Certifies 1492 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1297.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1493 : Certifies 1493 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1298.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1494 : Certifies 1494 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1299.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1495 : Certifies 1495 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1300.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1496 : Certifies 1496 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1301.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1497 : Certifies 1497 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1302.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1498 : Certifies 1498 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1303.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1499 : Certifies 1499 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1304.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B049 (j : Fin 30) :
    Certifies (1470 + j.val) := by
  fin_cases j
  · exact projection_1470
  · exact projection_1471
  · exact projection_1472
  · exact projection_1473
  · exact projection_1474
  · exact projection_1475
  · exact projection_1476
  · exact projection_1477
  · exact projection_1478
  · exact projection_1479
  · exact projection_1480
  · exact projection_1481
  · exact projection_1482
  · exact projection_1483
  · exact projection_1484
  · exact projection_1485
  · exact projection_1486
  · exact projection_1487
  · exact projection_1488
  · exact projection_1489
  · exact projection_1490
  · exact projection_1491
  · exact projection_1492
  · exact projection_1493
  · exact projection_1494
  · exact projection_1495
  · exact projection_1496
  · exact projection_1497
  · exact projection_1498
  · exact projection_1499

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
