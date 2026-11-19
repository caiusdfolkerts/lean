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
/- Source: ProjectionCertificates/R_one_six_1527.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1527

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 195, 677, 817, 465, 897, 654, 842, 962, 812, 376, 7, 27, 67, 131, 37, 133, 49, 81, 273, 545, 193, 385, 641, 769, 14, 134, 74, 522, 194, 834, 642, 44, 524, 548, 644, 56, 88, 296, 328, 776, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_195, vertices_677, vertices_817, vertices_465, vertices_897, vertices_654, vertices_842, vertices_962, vertices_812, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_273, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_522, vertices_194, vertices_834, vertices_642, vertices_44, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_195), (false, vertices_677), (false, vertices_817), (false, vertices_465), (false, vertices_897), (true, vertices_522), (true, vertices_834), (true, vertices_642), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_677) then 14 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (false, vertices_465) then 18 else
  if p.val = (false, vertices_897) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_834) then 11 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_776) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 0 5 7 8 834
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 74 842 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1527

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1528.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1528

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 93, 197, 389, 961, 422, 810, 244, 184, 728, 936, 7, 11, 515, 29, 69, 133, 261, 73, 193, 577, 385, 769, 38, 262, 42, 522, 290, 770, 52, 84, 164, 196, 388, 56, 88, 152, 168, 808, 584, 648, 176, 208, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_93, vertices_197, vertices_389, vertices_961, vertices_422, vertices_810, vertices_244, vertices_184, vertices_728, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_29, vertices_69, vertices_133, vertices_261, vertices_73, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_42, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_152, vertices_168, vertices_808, vertices_584, vertices_648, vertices_176, vertices_208, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_93), (false, vertices_197), (false, vertices_389), (false, vertices_961), (true, vertices_290), (true, vertices_164), (true, vertices_152), (true, vertices_168), (true, vertices_808), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_808) then 17 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
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
cert_row_4 0 0 1 4 6 7 422 38 3
cert_row_2 1 2 4 7 8 808
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 38 422 3
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 2 1 3 4 5 52 244 3
cert_coverFacet 3 184
cert_cover_2 3 3 2 4 6 56 184 3
cert_coverFacet 4 728
cert_cover_5 4 3 2 3 5 6 88 728 3
cert_coverFacet 5 936
cert_cover_5 5 1 2 4 6 7 168 936 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1528

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1529.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1529

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 93, 197, 389, 961, 422, 810, 244, 696, 728, 928, 7, 11, 515, 29, 69, 133, 261, 73, 193, 577, 385, 769, 38, 262, 42, 522, 290, 770, 52, 84, 164, 196, 388, 56, 88, 664, 552, 584, 176, 208, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_93, vertices_197, vertices_389, vertices_961, vertices_422, vertices_810, vertices_244, vertices_696, vertices_728, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_29, vertices_69, vertices_133, vertices_261, vertices_73, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_42, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_664, vertices_552, vertices_584, vertices_176, vertices_208, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_93), (false, vertices_197), (false, vertices_389), (false, vertices_961), (true, vertices_290), (true, vertices_164), (true, vertices_664), (true, vertices_552), (true, vertices_176), (true, vertices_208), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_664) then 17 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
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
cert_row_4 0 1 3 4 5 6 244 52 3
cert_row_2 1 2 3 6 8 664
cert_row_4 2 0 1 4 6 7 422 38 3
cert_row_4 3 0 2 4 7 8 810 42 3
cert_rows
cert_pivot_2 5 3 1 0
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 38 422 3
cert_coverFacet 1 810
cert_cover_5 1 3 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 0 1 3 4 5 52 244 3
cert_coverFacet 3 696
cert_cover_5 3 1 2 3 4 6 56 696 3
cert_coverFacet 4 728
cert_cover_5 4 1 2 3 5 6 88 728 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1529

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1530.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1530

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 93, 197, 389, 961, 422, 810, 244, 440, 472, 840, 7, 11, 515, 29, 69, 133, 261, 73, 193, 577, 385, 769, 38, 262, 42, 522, 290, 770, 52, 84, 164, 196, 388, 56, 88, 408, 296, 328, 584, 776, 176, 208, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_93, vertices_197, vertices_389, vertices_961, vertices_422, vertices_810, vertices_244, vertices_440, vertices_472, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_29, vertices_69, vertices_133, vertices_261, vertices_73, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_42, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_408, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_93), (false, vertices_197), (false, vertices_389), (false, vertices_961), (true, vertices_290), (true, vertices_164), (true, vertices_408), (true, vertices_296), (true, vertices_328), (true, vertices_776), (true, vertices_176), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_408) then 17 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
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
cert_row_2 1 2 3 6 7 408
cert_row_4 2 0 1 4 6 7 422 38 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 38 422 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 3 1 3 4 5 52 244 3
cert_coverFacet 3 440
cert_cover_5 3 1 2 3 4 6 56 440 3
cert_coverFacet 4 472
cert_cover_5 4 1 2 3 5 6 88 472 3
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1530

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1531.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1531

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 93, 197, 389, 961, 422, 810, 244, 312, 856, 496, 7, 11, 515, 29, 69, 133, 261, 73, 193, 577, 385, 769, 38, 262, 42, 522, 290, 770, 52, 84, 164, 196, 388, 56, 88, 280, 296, 584, 776, 240, 304, 336, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_93, vertices_197, vertices_389, vertices_961, vertices_422, vertices_810, vertices_244, vertices_312, vertices_856, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_29, vertices_69, vertices_133, vertices_261, vertices_73, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_42, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_280, vertices_296, vertices_584, vertices_776, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_93), (false, vertices_197), (false, vertices_389), (false, vertices_961), (true, vertices_290), (true, vertices_164), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
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
cert_row_4 0 0 1 4 6 7 422 38 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 38 422 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 1 1 3 4 5 52 244 3
cert_coverFacet 3 312
cert_cover_2 3 3 2 4 7 56 312 3
cert_coverFacet 4 856
cert_cover_5 4 3 2 3 5 7 88 856 3
cert_coverFacet 5 496
cert_cover_5 5 1 3 4 5 7 240 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1531

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1532.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1532

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 421, 809, 94, 198, 390, 962, 244, 440, 216, 968, 7, 11, 515, 37, 261, 41, 521, 289, 769, 30, 70, 134, 262, 74, 194, 578, 386, 770, 52, 84, 164, 196, 388, 56, 88, 152, 296, 200, 584, 392, 776, 176, 208, 416, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_421, vertices_809, vertices_94, vertices_198, vertices_390, vertices_962, vertices_244, vertices_440, vertices_216, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_37, vertices_261, vertices_41, vertices_521, vertices_289, vertices_769, vertices_30, vertices_70, vertices_134, vertices_262, vertices_74, vertices_194, vertices_578, vertices_386, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_152, vertices_296, vertices_200, vertices_584, vertices_392, vertices_776, vertices_176, vertices_208, vertices_416, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_421), (false, vertices_809), (true, vertices_70), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_392), (true, vertices_176), (true, vertices_208), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_960) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 5 6 7 8 960
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 56 440 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 968
cert_cover_5 7 1 2 5 6 7 200 968 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1532

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1533.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1533

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 587, 195, 293, 809, 961, 94, 198, 436, 724, 632, 944, 7, 11, 67, 131, 37, 261, 41, 521, 289, 193, 577, 385, 769, 30, 70, 134, 74, 194, 52, 84, 148, 292, 196, 388, 56, 88, 552, 584, 432, 560, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_587, vertices_195, vertices_293, vertices_809, vertices_961, vertices_94, vertices_198, vertices_436, vertices_724, vertices_632, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_37, vertices_261, vertices_41, vertices_521, vertices_289, vertices_193, vertices_577, vertices_385, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_587), (false, vertices_195), (false, vertices_293), (false, vertices_809), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_88), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1533

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1534.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1534

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 587, 195, 293, 809, 961, 94, 198, 244, 932, 696, 728, 7, 11, 67, 131, 37, 261, 41, 521, 289, 193, 577, 385, 769, 30, 70, 134, 74, 194, 52, 84, 164, 292, 196, 388, 56, 88, 664, 552, 584, 176, 208, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_587, vertices_195, vertices_293, vertices_809, vertices_961, vertices_94, vertices_198, vertices_244, vertices_932, vertices_696, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_37, vertices_261, vertices_41, vertices_521, vertices_289, vertices_193, vertices_577, vertices_385, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_664, vertices_552, vertices_584, vertices_176, vertices_208, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_587), (false, vertices_195), (false, vertices_293), (false, vertices_809), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_164), (true, vertices_196), (true, vertices_88), (true, vertices_664), (true, vertices_176), (true, vertices_208), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_664) then 17 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1534

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1535.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1535

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 805, 389, 625, 961, 398, 202, 300, 440, 728, 944, 7, 27, 67, 37, 133, 261, 49, 81, 545, 193, 577, 385, 769, 14, 134, 74, 138, 194, 44, 268, 292, 388, 56, 88, 152, 296, 200, 392, 432, 560, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_805, vertices_389, vertices_625, vertices_961, vertices_398, vertices_202, vertices_300, vertices_440, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_261, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_152, vertices_296, vertices_200, vertices_392, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_805), (false, vertices_389), (false, vertices_625), (false, vertices_961), (true, vertices_138), (true, vertices_268), (true, vertices_152), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_432), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_432) then 17 else
  if p.val = (true, vertices_656) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
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
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 440
cert_cover_5 3 0 2 3 4 6 56 440 3
cert_coverFacet 4 728
cert_cover_5 4 2 2 3 5 6 88 728 3
cert_coverFacet 5 944
cert_cover_5 5 0 3 4 6 8 432 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1535

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1536.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1536

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 293, 901, 817, 721, 398, 202, 300, 632, 488, 992, 7, 27, 67, 37, 133, 261, 49, 81, 529, 289, 193, 641, 769, 14, 134, 74, 138, 194, 44, 268, 292, 388, 56, 88, 104, 296, 200, 392, 560, 592, 480, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_293, vertices_901, vertices_817, vertices_721, vertices_398, vertices_202, vertices_300, vertices_632, vertices_488, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_261, vertices_49, vertices_81, vertices_529, vertices_289, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_104, vertices_296, vertices_200, vertices_392, vertices_560, vertices_592, vertices_480, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_293), (false, vertices_901), (false, vertices_817), (false, vertices_721), (true, vertices_138), (true, vertices_268), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_480), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_901) then 13 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_480) then 19 else
  if p.val = (true, vertices_608) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 4 5 6 7 480
cert_row_4 2 2 3 4 5 8 632 56 3
cert_rows_3
cert_pivot_3 6 0 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 632
cert_cover_5 3 2 2 3 4 5 56 632 3
cert_coverFacet 4 488
cert_cover_5 4 1 2 4 5 6 104 488 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 8 480 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1536

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1537.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1537

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 293, 817, 465, 206, 684, 932, 632, 968, 848, 7, 27, 67, 131, 37, 261, 49, 81, 273, 289, 193, 385, 14, 134, 74, 194, 44, 140, 676, 292, 388, 56, 88, 552, 200, 584, 648, 560, 336, 592, 784, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_293, vertices_817, vertices_465, vertices_206, vertices_684, vertices_932, vertices_632, vertices_968, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_676, vertices_292, vertices_388, vertices_56, vertices_88, vertices_552, vertices_200, vertices_584, vertices_648, vertices_560, vertices_336, vertices_592, vertices_784, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_293), (false, vertices_817), (false, vertices_465), (true, vertices_140), (true, vertices_676), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_592), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_676) then 15 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 4 6 8 676
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 932
cert_cover_5 2 1 1 4 6 7 676 932 3
cert_coverFacet 3 632
cert_cover_5 3 2 2 3 4 5 56 632 3
cert_coverFacet 4 968
cert_cover_5 4 3 2 5 6 7 200 968 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1537

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1538.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1538

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 293, 369, 961, 206, 684, 932, 824, 728, 848, 7, 27, 67, 131, 37, 261, 49, 81, 289, 193, 321, 385, 14, 134, 74, 194, 44, 140, 676, 292, 388, 56, 88, 536, 552, 200, 648, 304, 336, 592, 784, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_293, vertices_369, vertices_961, vertices_206, vertices_684, vertices_932, vertices_824, vertices_728, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_289, vertices_193, vertices_321, vertices_385, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_676, vertices_292, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_336, vertices_592, vertices_784, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_293), (false, vertices_369), (false, vertices_961), (true, vertices_140), (true, vertices_676), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_592), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_369) then 18 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_676) then 15 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 4 6 8 676
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 932
cert_cover_5 2 1 1 4 6 7 676 932 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 728
cert_cover_5 4 3 2 3 5 6 88 728 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1538

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1539.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1539

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 625, 961, 206, 300, 396, 440, 728, 944, 7, 27, 67, 131, 37, 261, 49, 81, 545, 193, 577, 385, 769, 14, 134, 74, 194, 44, 140, 268, 292, 388, 56, 88, 152, 296, 200, 392, 432, 560, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_625, vertices_961, vertices_206, vertices_300, vertices_396, vertices_440, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_152, vertices_296, vertices_200, vertices_392, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_625), (false, vertices_961), (true, vertices_140), (true, vertices_268), (true, vertices_152), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_432), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 15 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_432) then 17 else
  if p.val = (true, vertices_656) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_rows_3
cert_pivot_3 0 4 2
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 300
cert_cover_2 1 2 1 4 7 44 300 3
cert_coverFacet 2 396
cert_cover_2 2 2 1 6 7 140 396 3
cert_coverFacet 3 440
cert_cover_5 3 0 2 3 4 6 56 440 3
cert_coverFacet 4 728
cert_cover_5 4 2 2 3 5 6 88 728 3
cert_coverFacet 5 944
cert_cover_5 5 0 3 4 6 8 432 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1539

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1540.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1540

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 425, 94, 198, 564, 852, 452, 696, 728, 992, 7, 11, 131, 37, 261, 41, 137, 289, 385, 30, 70, 134, 74, 194, 52, 84, 532, 548, 196, 324, 388, 772, 56, 88, 664, 168, 200, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_425, vertices_94, vertices_198, vertices_564, vertices_852, vertices_452, vertices_696, vertices_728, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_289, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_324, vertices_388, vertices_772, vertices_56, vertices_88, vertices_664, vertices_168, vertices_200, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_425), (true, vertices_70), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_88), (true, vertices_664), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_664) then 20 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
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
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 852
cert_cover_5 3 2 1 3 5 7 84 852 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 728
cert_cover_5 6 1 2 3 5 6 88 728 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1540

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1541.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1541

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 425, 94, 198, 564, 724, 900, 376, 968, 880, 7, 11, 131, 37, 261, 41, 137, 289, 385, 30, 70, 134, 74, 194, 52, 84, 532, 548, 196, 388, 644, 772, 56, 88, 296, 200, 328, 392, 368, 560, 592, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_425, vertices_94, vertices_198, vertices_564, vertices_724, vertices_900, vertices_376, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_289, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_200, vertices_328, vertices_392, vertices_368, vertices_560, vertices_592, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_425), (true, vertices_70), (true, vertices_84), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_88), (true, vertices_328), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_368) then 21 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_2 1 3 4 5 7 368
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 900
cert_cover_2 4 6 1 7 8 388 900 3
cert_coverFacet 5 376
cert_cover_5 5 1 2 3 4 5 56 376 3
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 200 968 3
cert_coverFacet 7 880
cert_cover_5 7 1 3 4 5 8 368 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1541

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1542.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1542

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 425, 94, 198, 628, 964, 312, 728, 920, 816, 7, 11, 131, 37, 261, 41, 137, 289, 385, 30, 70, 134, 74, 194, 52, 84, 548, 196, 580, 388, 772, 56, 88, 664, 280, 296, 200, 392, 304, 560, 592, 784, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_425, vertices_94, vertices_198, vertices_628, vertices_964, vertices_312, vertices_728, vertices_920, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_289, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_664, vertices_280, vertices_296, vertices_200, vertices_392, vertices_304, vertices_560, vertices_592, vertices_784, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_425), (true, vertices_70), (true, vertices_84), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_664), (true, vertices_280), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_664) then 20 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
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
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 728
cert_cover_5 5 1 2 3 5 6 88 728 3
cert_coverFacet 6 920
cert_cover_5 6 1 2 3 6 7 664 920 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1542

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1543.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1543

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 425, 94, 198, 628, 708, 900, 824, 472, 976, 7, 11, 131, 37, 261, 41, 137, 289, 385, 30, 70, 134, 74, 194, 52, 84, 548, 196, 580, 388, 644, 772, 56, 88, 280, 296, 200, 392, 560, 464, 592, 784, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_425, vertices_94, vertices_198, vertices_628, vertices_708, vertices_900, vertices_824, vertices_472, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_289, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_200, vertices_392, vertices_560, vertices_464, vertices_592, vertices_784, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_425), (true, vertices_70), (true, vertices_84), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_88), (true, vertices_280), (true, vertices_560), (true, vertices_464), (true, vertices_592), (true, vertices_784), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_464) then 21 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 628
cert_cover_5 2 2 1 3 4 5 52 628 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 900
cert_cover_2 4 6 1 7 8 388 900 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 472
cert_cover_5 6 0 2 3 5 6 88 472 3
cert_coverFacet 7 976
cert_cover_5 7 0 3 5 6 8 464 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1543

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1544.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1544

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 425, 94, 198, 628, 964, 824, 216, 920, 720, 7, 11, 131, 37, 261, 41, 137, 289, 385, 30, 70, 134, 74, 194, 52, 84, 548, 196, 580, 388, 772, 56, 88, 152, 792, 296, 200, 392, 560, 208, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_425, vertices_94, vertices_198, vertices_628, vertices_964, vertices_824, vertices_216, vertices_920, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_289, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_88, vertices_152, vertices_792, vertices_296, vertices_200, vertices_392, vertices_560, vertices_208, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_425), (true, vertices_70), (true, vertices_84), (true, vertices_196), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_792), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_792) then 20 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
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
cert_coverFacet 5 216
cert_cover_2 5 3 2 5 6 88 216 3
cert_coverFacet 6 920
cert_cover_5 6 1 2 3 6 7 152 920 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1544

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1545.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1545

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 625, 961, 206, 428, 440, 728, 816, 912, 7, 27, 67, 131, 37, 261, 49, 81, 545, 193, 577, 385, 769, 14, 134, 74, 194, 44, 140, 292, 388, 56, 88, 152, 424, 200, 304, 560, 592, 400, 656, 784, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_625, vertices_961, vertices_206, vertices_428, vertices_440, vertices_728, vertices_816, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_292, vertices_388, vertices_56, vertices_88, vertices_152, vertices_424, vertices_200, vertices_304, vertices_560, vertices_592, vertices_400, vertices_656, vertices_784, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_625), (false, vertices_961), (true, vertices_140), (true, vertices_152), (true, vertices_424), (true, vertices_200), (true, vertices_304), (true, vertices_400), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_625) then 17 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_424) then 15 else
  if p.val = (true, vertices_200) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
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
cert_coverFacet 2 440
cert_cover_5 2 0 2 3 4 6 56 440 3
cert_coverFacet 3 728
cert_cover_5 3 2 2 3 5 6 88 728 3
cert_coverFacet 4 816
cert_cover_2 4 4 3 7 8 304 816 3
cert_coverFacet 5 912
cert_cover_2 5 6 3 7 8 400 912 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1545

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1546.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1546

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 681, 897, 94, 198, 372, 452, 824, 728, 976, 7, 11, 131, 37, 261, 41, 137, 545, 385, 641, 769, 30, 70, 134, 74, 194, 52, 84, 292, 196, 324, 388, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_681, vertices_897, vertices_94, vertices_198, vertices_372, vertices_452, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_681), (false, vertices_897), (true, vertices_70), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_88), (true, vertices_536), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_720) then 20 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 897 70 84 196 324 88 536 304 336 784 448 391 203 805 681 720
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 372
cert_cover_5 2 2 1 3 4 5 52 372 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 728
cert_cover_5 5 0 2 3 5 6 88 728 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1546

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1547.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1547

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 681, 897, 94, 198, 308, 468, 632, 968, 880, 7, 11, 131, 37, 261, 41, 137, 545, 385, 641, 769, 30, 70, 134, 74, 194, 52, 84, 276, 292, 196, 388, 56, 88, 552, 200, 584, 648, 624, 304, 336, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_681, vertices_897, vertices_94, vertices_198, vertices_308, vertices_468, vertices_632, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_276, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_200, vertices_584, vertices_648, vertices_624, vertices_304, vertices_336, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_681), (false, vertices_897), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_88), (true, vertices_584), (true, vertices_624), (true, vertices_304), (true, vertices_336), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_624) then 20 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 897 70 84 276 196 88 584 304 336 448 832 391 203 805 681 624
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 8 624
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 308
cert_cover_2 2 3 1 4 7 52 308 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 632
cert_cover_5 4 0 2 3 4 5 56 632 3
cert_coverFacet 5 968
cert_cover_5 5 3 2 5 6 7 200 968 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 624 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1547

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1548.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1548

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 817, 465, 206, 684, 900, 632, 968, 848, 7, 27, 67, 131, 37, 261, 49, 81, 273, 801, 193, 385, 14, 134, 74, 194, 44, 140, 548, 388, 644, 772, 56, 88, 552, 200, 584, 648, 560, 336, 592, 784, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_817, vertices_465, vertices_206, vertices_684, vertices_900, vertices_632, vertices_968, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_273, vertices_801, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_552, vertices_200, vertices_584, vertices_648, vertices_560, vertices_336, vertices_592, vertices_784, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_817), (false, vertices_465), (true, vertices_140), (true, vertices_644), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_592), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
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
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 900
cert_cover_2 2 6 1 7 8 388 900 3
cert_coverFacet 3 632
cert_cover_5 3 2 2 3 4 5 56 632 3
cert_coverFacet 4 968
cert_cover_5 4 3 2 5 6 7 200 968 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1548

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1549.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1549

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 293, 361, 961, 94, 198, 436, 724, 632, 944, 864, 7, 11, 131, 37, 261, 41, 73, 289, 193, 321, 385, 30, 70, 134, 74, 194, 52, 84, 148, 292, 196, 388, 56, 88, 104, 432, 560, 592, 656, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_293, vertices_361, vertices_961, vertices_94, vertices_198, vertices_436, vertices_724, vertices_632, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_73, vertices_289, vertices_193, vertices_321, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_104, vertices_432, vertices_560, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_293), (false, vertices_361), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_88), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_432) then 19 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 52 436 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 944
cert_cover_5 5 1 3 4 6 8 432 944 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1549

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1550.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1550

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 293, 361, 961, 94, 198, 564, 724, 932, 824, 856, 7, 11, 131, 37, 261, 41, 73, 289, 193, 321, 385, 30, 70, 134, 74, 194, 52, 84, 532, 292, 548, 196, 388, 644, 56, 88, 792, 296, 328, 560, 592, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_293, vertices_361, vertices_961, vertices_94, vertices_198, vertices_564, vertices_724, vertices_932, vertices_824, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_73, vertices_289, vertices_193, vertices_321, vertices_385, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_532, vertices_292, vertices_548, vertices_196, vertices_388, vertices_644, vertices_56, vertices_88, vertices_792, vertices_296, vertices_328, vertices_560, vertices_592, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_293), (false, vertices_361), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_532), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_88), (true, vertices_792), (true, vertices_560), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_792) then 18 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_2 1 2 3 7 8 792
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 1 4 6 7 8 932 292 2
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 932
cert_cover_5 4 3 1 4 6 7 292 932 2
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 856
cert_cover_5 6 1 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1550

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1551.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1551

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 293, 809, 585, 961, 94, 198, 436, 724, 632, 944, 7, 11, 131, 37, 261, 41, 73, 521, 289, 193, 577, 385, 769, 30, 70, 134, 74, 194, 52, 84, 148, 292, 196, 388, 56, 88, 552, 584, 432, 560, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_293, vertices_809, vertices_585, vertices_961, vertices_94, vertices_198, vertices_436, vertices_724, vertices_632, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_73, vertices_521, vertices_289, vertices_193, vertices_577, vertices_385, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_293), (false, vertices_809), (false, vertices_585), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_88), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1551

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1552.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1552

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 617, 961, 94, 198, 436, 212, 824, 856, 464, 7, 11, 131, 37, 261, 41, 73, 545, 193, 577, 385, 769, 30, 70, 134, 74, 194, 52, 84, 148, 292, 196, 388, 56, 88, 792, 552, 584, 304, 208, 336, 400, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_617, vertices_961, vertices_94, vertices_198, vertices_436, vertices_212, vertices_824, vertices_856, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_73, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_792, vertices_552, vertices_584, vertices_304, vertices_208, vertices_336, vertices_400, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_617), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_88), (true, vertices_792), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_792) then 17 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
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
cert_row_2 1 2 3 7 8 792
cert_row_4 2 1 3 4 6 7 436 52 3
cert_rows_3
cert_pivot_3 2 0 1
cert_heightProof 3
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 436
cert_cover_5 2 2 1 3 4 6 52 436 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1552

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1553.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1553

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 805, 617, 961, 94, 198, 436, 212, 824, 600, 976, 7, 11, 131, 37, 261, 41, 73, 545, 193, 577, 385, 769, 30, 70, 134, 74, 194, 52, 84, 148, 292, 196, 388, 56, 88, 536, 552, 584, 304, 208, 592, 400, 784, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_805, vertices_617, vertices_961, vertices_94, vertices_198, vertices_436, vertices_212, vertices_824, vertices_600, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_73, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_304, vertices_208, vertices_592, vertices_400, vertices_784, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_805), (false, vertices_617), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_88), (true, vertices_536), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_2 1 5 6 7 8 960
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 436
cert_cover_5 2 2 1 3 4 6 52 436 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1553

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1554.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1554

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 139, 805, 681, 961, 94, 198, 714, 372, 452, 824, 856, 7, 11, 131, 37, 261, 41, 137, 545, 385, 641, 769, 30, 70, 134, 74, 138, 194, 52, 84, 292, 196, 324, 388, 56, 88, 792, 552, 584, 648, 304, 336, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_139, vertices_805, vertices_681, vertices_961, vertices_94, vertices_198, vertices_714, vertices_372, vertices_452, vertices_824, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_138, vertices_194, vertices_52, vertices_84, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_792, vertices_552, vertices_584, vertices_648, vertices_304, vertices_336, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_139), (false, vertices_805), (false, vertices_681), (false, vertices_961), (true, vertices_70), (true, vertices_74), (true, vertices_194), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_88), (true, vertices_792), (true, vertices_584), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 20 21 23 24 25
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
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_792) then 18 else
  if p.val = (true, vertices_584) then 8 else
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
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
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
  | 18 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
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
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_2 1 0 1 2 3 30
cert_row_2 2 2 3 7 8 792
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 74 714 3
cert_coverFacet 3 372
cert_cover_5 3 3 1 3 4 5 52 372 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1554

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1555.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1555

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 805, 305, 465, 142, 714, 684, 964, 824, 856, 7, 27, 67, 131, 37, 261, 49, 81, 273, 289, 193, 385, 14, 134, 74, 138, 194, 44, 140, 548, 388, 644, 772, 56, 88, 792, 552, 584, 648, 304, 336, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_805, vertices_305, vertices_465, vertices_142, vertices_714, vertices_684, vertices_964, vertices_824, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_792, vertices_552, vertices_584, vertices_648, vertices_304, vertices_336, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_305), (false, vertices_465), (true, vertices_138), (true, vertices_140), (true, vertices_644), (true, vertices_792), (true, vertices_552), (true, vertices_584), (true, vertices_648), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_792) then 17 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
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
  | 15 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 7 8 792
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 1 5 6 7 8 964 388 1
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 74 714 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 964
cert_cover_5 3 3 1 5 6 7 388 964 1
cert_coverFacet 4 824
cert_cover_5 4 0 2 3 4 7 56 824 3
cert_coverFacet 5 856
cert_cover_5 5 0 2 3 5 7 88 856 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1555

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1556.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1556

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 139, 805, 681, 961, 94, 198, 714, 308, 468, 376, 872, 7, 11, 131, 37, 261, 41, 137, 545, 385, 641, 769, 30, 70, 134, 74, 138, 194, 52, 84, 276, 292, 196, 388, 56, 88, 360, 552, 584, 648, 304, 336, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_139, vertices_805, vertices_681, vertices_961, vertices_94, vertices_198, vertices_714, vertices_308, vertices_468, vertices_376, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_261, vertices_41, vertices_137, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_138, vertices_194, vertices_52, vertices_84, vertices_276, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_360, vertices_552, vertices_584, vertices_648, vertices_304, vertices_336, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_139), (false, vertices_805), (false, vertices_681), (false, vertices_961), (true, vertices_70), (true, vertices_74), (true, vertices_194), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_88), (true, vertices_360), (true, vertices_584), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 20 21 23 24 25
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
  if p.val = (true, vertices_360) then 18 else
  if p.val = (true, vertices_584) then 8 else
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
  | 18 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
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
cert_row_2 0 2 4 5 7 360
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
cert_coverFacet 5 376
cert_cover_5 5 0 2 3 4 5 56 376 3
cert_coverFacet 6 872
cert_cover_5 6 0 2 4 5 8 360 872 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1556

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1680 : Certifies 1680 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1527.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1681 : Certifies 1681 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1528.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1682 : Certifies 1682 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1529.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1683 : Certifies 1683 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1530.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1684 : Certifies 1684 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1531.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1685 : Certifies 1685 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1532.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1686 : Certifies 1686 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1533.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1687 : Certifies 1687 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1534.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1688 : Certifies 1688 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1535.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1689 : Certifies 1689 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1536.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1690 : Certifies 1690 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1537.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1691 : Certifies 1691 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1538.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1692 : Certifies 1692 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1539.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1693 : Certifies 1693 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1540.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1694 : Certifies 1694 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1541.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1695 : Certifies 1695 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1542.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1696 : Certifies 1696 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1543.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1697 : Certifies 1697 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1544.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1698 : Certifies 1698 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1545.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1699 : Certifies 1699 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1546.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1700 : Certifies 1700 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1547.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1701 : Certifies 1701 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1548.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1702 : Certifies 1702 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1549.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1703 : Certifies 1703 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1550.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1704 : Certifies 1704 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1551.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1705 : Certifies 1705 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1552.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1706 : Certifies 1706 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1553.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1707 : Certifies 1707 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1554.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1708 : Certifies 1708 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1555.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1709 : Certifies 1709 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1556.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B056 (j : Fin 30) :
    Certifies (1680 + j.val) := by
  fin_cases j
  · exact projection_1680
  · exact projection_1681
  · exact projection_1682
  · exact projection_1683
  · exact projection_1684
  · exact projection_1685
  · exact projection_1686
  · exact projection_1687
  · exact projection_1688
  · exact projection_1689
  · exact projection_1690
  · exact projection_1691
  · exact projection_1692
  · exact projection_1693
  · exact projection_1694
  · exact projection_1695
  · exact projection_1696
  · exact projection_1697
  · exact projection_1698
  · exact projection_1699
  · exact projection_1700
  · exact projection_1701
  · exact projection_1702
  · exact projection_1703
  · exact projection_1704
  · exact projection_1705
  · exact projection_1706
  · exact projection_1707
  · exact projection_1708
  · exact projection_1709

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
