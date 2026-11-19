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
/- Source: ProjectionCertificates/R_multi_six_0083.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0083

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 835, 341, 553, 817, 206, 962, 252, 936, 496, 7, 11, 67, 515, 21, 69, 41, 521, 49, 273, 545, 321, 769, 14, 70, 138, 194, 834, 642, 60, 204, 84, 168, 552, 648, 240, 304, 336, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_835, vertices_341, vertices_553, vertices_817, vertices_206, vertices_962, vertices_252, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_321, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_834, vertices_642, vertices_60, vertices_204, vertices_84, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_835), (false, vertices_341), (false, vertices_553), (false, vertices_817), (true, vertices_194), (true, vertices_204), (true, vertices_168), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 14 15 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 8 else
  if p.val = (false, vertices_835) then 9 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_896) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 2
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
cert_coverFacet 4 496
cert_cover 4 5 2 3 4 3 1 7 3 240 496 240 60 252 5
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0083

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_multi_six_0084.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0084

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 203, 653, 961, 534, 250, 850, 172, 820, 932, 496, 7, 11, 67, 13, 517, 137, 193, 577, 641, 22, 518, 58, 202, 82, 530, 578, 44, 140, 52, 532, 164, 804, 644, 168, 240, 304, 336, 784, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_534, vertices_250, vertices_850, vertices_172, vertices_820, vertices_932, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_530, vertices_578, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_804, vertices_644, vertices_168, vertices_240, vertices_304, vertices_336, vertices_784, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_530), (true, vertices_532), (true, vertices_164), (true, vertices_804), (true, vertices_168), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_804) then 15 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
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
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 932
cert_cover_5 5 0 1 4 6 7 164 932 3
cert_coverFacet 6 496
cert_cover 6 5 2 3 4 3 0 7 3 240 496 240 58 250 5
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0084

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_multi_six_0086.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0086

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 651, 341, 553, 817, 833, 206, 962, 252, 936, 496, 7, 11, 515, 21, 69, 41, 521, 49, 273, 545, 321, 577, 769, 14, 70, 138, 194, 578, 642, 60, 204, 84, 168, 552, 648, 240, 304, 336, 416, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_651, vertices_341, vertices_553, vertices_817, vertices_833, vertices_206, vertices_962, vertices_252, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_578, vertices_642, vertices_60, vertices_204, vertices_84, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_651), (false, vertices_341), (false, vertices_553), (false, vertices_817), (false, vertices_833), (true, vertices_194), (true, vertices_204), (true, vertices_168), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 14 15 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_583) then 8 else
  if p.val = (false, vertices_651) then 9 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_896) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 2
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0086

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_multi_six_0087.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0087

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 651, 341, 553, 817, 206, 326, 962, 252, 936, 496, 7, 11, 515, 21, 261, 41, 521, 49, 273, 545, 769, 14, 70, 262, 138, 194, 322, 642, 770, 60, 204, 84, 324, 168, 552, 648, 240, 304, 336, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_651, vertices_341, vertices_553, vertices_817, vertices_206, vertices_326, vertices_962, vertices_252, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_261, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_262, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_60, vertices_204, vertices_84, vertices_324, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_651), (false, vertices_341), (false, vertices_553), (false, vertices_817), (true, vertices_70), (true, vertices_194), (true, vertices_322), (true, vertices_204), (true, vertices_168), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_204) then 14 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
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
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0087

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_multi_six_0088.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0088

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 459, 213, 121, 782, 898, 812, 692, 360, 880, 976, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 518, 266, 386, 642, 770, 44, 780, 52, 148, 548, 644, 104, 296, 328, 112, 560, 208, 848, 656, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_459, vertices_213, vertices_121, vertices_782, vertices_898, vertices_812, vertices_692, vertices_360, vertices_880, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_52, vertices_148, vertices_548, vertices_644, vertices_104, vertices_296, vertices_328, vertices_112, vertices_560, vertices_208, vertices_848, vertices_656, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_459), (false, vertices_213), (false, vertices_121), (true, vertices_770), (true, vertices_780), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_848), (true, vertices_656), (true, vertices_352), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 13 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 9 else
  if p.val = (false, vertices_459) then 15 else
  if p.val = (false, vertices_213) then 11 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_780) then 12 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_848) then 18 else
  if p.val = (true, vertices_656) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_459), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_848), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_2 1 3 5 7 8 848
cert_row_4 2 1 3 4 6 8 692 52 3
cert_rows_3
cert_pivot_3 5 2 1
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 880
cert_cover_5 5 1 3 4 5 7 112 880 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0088

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_multi_six_0089.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0089

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 725, 121, 201, 782, 962, 812, 564, 488, 880, 7, 11, 131, 21, 645, 57, 73, 137, 81, 193, 14, 518, 266, 386, 642, 770, 44, 780, 52, 532, 548, 104, 296, 200, 392, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_725, vertices_121, vertices_201, vertices_782, vertices_962, vertices_812, vertices_564, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_645, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_52, vertices_532, vertices_548, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_725), (false, vertices_121), (false, vertices_201), (true, vertices_770), (true, vertices_780), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_352), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 15 11 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_395) then 10 else
  if p.val = (false, vertices_725) then 18 else
  if p.val = (false, vertices_121) then 13 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_780) then 14 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_725), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 488
cert_cover_5 4 2 2 4 5 6 104 488 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0089

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_multi_six_0090.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0090

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 725, 121, 201, 782, 962, 300, 820, 488, 880, 7, 11, 131, 21, 645, 57, 73, 137, 81, 193, 14, 518, 266, 386, 642, 770, 44, 268, 52, 532, 292, 772, 104, 296, 200, 392, 112, 816, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_725, vertices_121, vertices_201, vertices_782, vertices_962, vertices_300, vertices_820, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_645, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_816, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_725), (false, vertices_121), (false, vertices_201), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_296), (true, vertices_816), (true, vertices_352), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 13 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_395) then 10 else
  if p.val = (false, vertices_725) then 17 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_725), by decide +kernel⟩
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
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 386 962 1
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 488
cert_cover_5 4 3 2 4 5 6 104 488 3
cert_coverFacet 5 880
cert_cover_5 5 0 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0090

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_multi_six_0091.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0091

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 789, 121, 849, 398, 962, 940, 564, 232, 752, 7, 11, 67, 21, 261, 57, 73, 81, 785, 321, 14, 262, 138, 194, 322, 386, 44, 396, 52, 532, 548, 772, 104, 168, 200, 112, 560, 592, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_789, vertices_121, vertices_849, vertices_398, vertices_962, vertices_940, vertices_564, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_785, vertices_321, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_849), (true, vertices_386), (true, vertices_396), (true, vertices_548), (true, vertices_168), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 13 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_327) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_396) then 12 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_224) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 2 4 6 7 940 44 3
cert_row_4 2 1 2 4 6 8 940 44 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover 0 2 2 0 1 3 1 6 4 14 398 396 44 940 6
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 940
cert_cover_2 2 2 1 4 6 44 940 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0091

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_multi_six_0092.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0092

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 853, 121, 398, 962, 812, 564, 232, 936, 752, 7, 11, 67, 21, 325, 57, 73, 81, 14, 262, 138, 194, 322, 386, 44, 268, 52, 532, 548, 772, 104, 168, 808, 200, 392, 112, 560, 592, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_853, vertices_121, vertices_398, vertices_962, vertices_812, vertices_564, vertices_232, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_325, vertices_57, vertices_73, vertices_81, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_168, vertices_808, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_853), (false, vertices_121), (true, vertices_386), (true, vertices_268), (true, vertices_548), (true, vertices_168), (true, vertices_808), (true, vertices_392), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 18 14 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_853) then 16 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_808) then 19 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_853), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 2 4 7 8 808
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 194 962 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 936
cert_cover_5 5 1 2 4 6 7 168 936 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0092

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_multi_six_0093.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0093

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 361, 526, 902, 668, 212, 824, 1008, 7, 11, 195, 259, 53, 69, 41, 265, 97, 321, 14, 134, 518, 522, 386, 770, 28, 524, 84, 148, 196, 644, 56, 536, 296, 776, 112, 816, 208, 656, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_668, vertices_212, vertices_824, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_148, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_816, vertices_208, vertices_656, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_148), (true, vertices_644), (true, vertices_536), (true, vertices_816), (true, vertices_208), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 8 10 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_117) then 9 else
  if p.val = (false, vertices_361) then 13 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 2 3 6 8 668 28 3
cert_row_4 2 3 4 5 6 7 1008 112 3
cert_row_4 3 3 4 5 6 8 1008 112 3
cert_rows
cert_pivot_2 0 1 7 4
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 824
cert_cover 4 4 4 2 3 3 3 7 5 56 824 816 112 1008 6
cert_coverFacet 5 1008
cert_cover_2 5 4 3 5 6 112 1008 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0093

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_multi_six_0094.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0094

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 361, 526, 902, 540, 724, 952, 496, 7, 11, 195, 259, 53, 69, 41, 265, 97, 321, 14, 134, 518, 522, 386, 770, 28, 524, 84, 532, 196, 644, 56, 536, 296, 776, 112, 432, 208, 656, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_952, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_432, vertices_208, vertices_656, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_432), (true, vertices_208), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 8 10 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_117) then 9 else
  if p.val = (false, vertices_361) then 13 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 3 4 6 7 952 56 3
cert_row_4 3 2 3 4 6 8 952 56 3
cert_rows
cert_pivot_2 0 1 7 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 952
cert_cover_2 4 3 2 4 6 56 952 3
cert_coverFacet 5 496
cert_cover 5 5 3 3 4 3 2 6 4 112 496 432 56 952 6
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0094

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_multi_six_0095.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0095

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 459, 213, 121, 526, 906, 812, 692, 360, 880, 976, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 518, 394, 522, 642, 44, 524, 52, 148, 548, 644, 104, 296, 328, 776, 112, 560, 208, 848, 656, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_459, vertices_213, vertices_121, vertices_526, vertices_906, vertices_812, vertices_692, vertices_360, vertices_880, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_518, vertices_394, vertices_522, vertices_642, vertices_44, vertices_524, vertices_52, vertices_148, vertices_548, vertices_644, vertices_104, vertices_296, vertices_328, vertices_776, vertices_112, vertices_560, vertices_208, vertices_848, vertices_656, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_459), (false, vertices_213), (false, vertices_121), (true, vertices_522), (true, vertices_524), (true, vertices_548), (true, vertices_296), (true, vertices_776), (true, vertices_560), (true, vertices_848), (true, vertices_656), (true, vertices_352), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 14 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_459) then 16 else
  if p.val = (false, vertices_213) then 13 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_848) then 19 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_459), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_848), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_2 1 3 5 7 8 848
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 0 5 2 1
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 8 394 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 692
cert_cover_5 3 3 1 3 4 6 52 692 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 880
cert_cover_5 5 1 3 4 5 7 112 880 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0095

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_multi_six_0096.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0096

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 459, 213, 121, 526, 906, 556, 820, 916, 872, 496, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 518, 394, 522, 642, 44, 524, 52, 148, 788, 548, 644, 104, 552, 328, 776, 112, 304, 208, 400, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_459, vertices_213, vertices_121, vertices_526, vertices_906, vertices_556, vertices_820, vertices_916, vertices_872, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_518, vertices_394, vertices_522, vertices_642, vertices_44, vertices_524, vertices_52, vertices_148, vertices_788, vertices_548, vertices_644, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_459), (false, vertices_213), (false, vertices_121), (true, vertices_522), (true, vertices_524), (true, vertices_788), (true, vertices_548), (true, vertices_552), (true, vertices_776), (true, vertices_304), (true, vertices_400), (true, vertices_352), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 16 12 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_459) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_788) then 18 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_459), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_2 1 1 3 7 8 788
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 8 394 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 148 916 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0096

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_multi_six_0097.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0097

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 459, 213, 121, 782, 962, 812, 692, 360, 880, 720, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 518, 266, 450, 642, 770, 44, 780, 52, 148, 548, 644, 104, 296, 328, 112, 560, 208, 592, 656, 352, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_459, vertices_213, vertices_121, vertices_782, vertices_962, vertices_812, vertices_692, vertices_360, vertices_880, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_518, vertices_266, vertices_450, vertices_642, vertices_770, vertices_44, vertices_780, vertices_52, vertices_148, vertices_548, vertices_644, vertices_104, vertices_296, vertices_328, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_459), (false, vertices_213), (false, vertices_121), (true, vertices_770), (true, vertices_780), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_352), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_459) then 17 else
  if p.val = (false, vertices_213) then 13 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_780) then 14 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_459), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 7 450
cert_row_2 1 1 2 7 8 780
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 8 450 962 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0097

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_multi_six_0098.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0098

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 75, 835, 341, 249, 526, 714, 812, 436, 936, 976, 7, 11, 67, 771, 21, 261, 57, 73, 81, 321, 14, 518, 74, 522, 578, 44, 524, 52, 276, 292, 772, 168, 808, 200, 648, 176, 208, 336, 400, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_75, vertices_835, vertices_341, vertices_249, vertices_526, vertices_714, vertices_812, vertices_436, vertices_936, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_74, vertices_522, vertices_578, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_168, vertices_808, vertices_200, vertices_648, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_75), (false, vertices_835), (false, vertices_341), (false, vertices_249), (true, vertices_522), (true, vertices_524), (true, vertices_292), (true, vertices_808), (true, vertices_648), (true, vertices_400), (true, vertices_416), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 14 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_808) then 17 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_2 1 2 4 7 8 808
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 52 436 3
cert_coverFacet 4 936
cert_cover_5 4 1 2 4 6 7 168 936 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0098

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_multi_six_0099.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0099

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 331, 597, 249, 782, 962, 428, 820, 456, 944, 720, 7, 11, 67, 21, 581, 57, 73, 81, 14, 518, 266, 322, 578, 770, 44, 268, 52, 532, 292, 772, 168, 200, 328, 392, 176, 816, 208, 592, 656, 416, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_331, vertices_597, vertices_249, vertices_782, vertices_962, vertices_428, vertices_820, vertices_456, vertices_944, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_581, vertices_57, vertices_73, vertices_81, vertices_14, vertices_518, vertices_266, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_168, vertices_200, vertices_328, vertices_392, vertices_176, vertices_816, vertices_208, vertices_592, vertices_656, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_331), (false, vertices_597), (false, vertices_249), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_392), (true, vertices_816), (true, vertices_656), (true, vertices_416), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_583) then 13 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_249) then 20 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 322 962 2
cert_coverFacet 2 428
cert_cover_5 2 3 1 2 4 6 44 428 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 456
cert_cover_2 4 5 2 6 7 200 456 3
cert_coverFacet 5 944
cert_cover_5 5 0 3 4 6 7 176 944 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0099

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_multi_six_0100.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0100

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 341, 249, 654, 202, 962, 684, 820, 944, 464, 7, 11, 259, 21, 261, 57, 73, 81, 321, 14, 518, 74, 138, 194, 322, 642, 770, 44, 652, 52, 276, 548, 772, 168, 200, 176, 816, 208, 336, 400, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_341, vertices_249, vertices_654, vertices_202, vertices_962, vertices_684, vertices_820, vertices_944, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_74, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_200, vertices_176, vertices_816, vertices_208, vertices_336, vertices_400, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_341), (false, vertices_249), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_816), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_331) then 10 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_652) then 13 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_400) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_2 1 3 4 7 8 816
cert_row_4 2 0 5 6 7 8 962 194 3
cert_rows_3
cert_pivot_3 3 1 0
cert_heightProof 3
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 52 820 3
cert_coverFacet 5 944
cert_cover_5 5 1 3 4 6 7 176 944 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0100

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_multi_six_0101.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0101

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 341, 249, 654, 202, 962, 684, 820, 688, 976, 7, 11, 259, 21, 261, 57, 73, 81, 321, 14, 518, 74, 138, 194, 322, 642, 770, 44, 652, 52, 276, 548, 772, 168, 200, 176, 560, 208, 336, 656, 784, 672, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_341, vertices_249, vertices_654, vertices_202, vertices_962, vertices_684, vertices_820, vertices_688, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_74, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_200, vertices_176, vertices_560, vertices_208, vertices_336, vertices_656, vertices_784, vertices_672, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_341), (false, vertices_249), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_560), (true, vertices_656), (true, vertices_784), (true, vertices_672), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 17 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_331) then 10 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_249) then 18 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_652) then 13 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_960) then 20 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_2 1 5 6 7 8 960
cert_row_4 2 1 3 4 7 8 820 52 3
cert_rows_3
cert_pivot_3 5 2 1
cert_heightProof 3
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 688
cert_cover_2 5 4 3 6 8 176 688 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0101

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_multi_six_0102.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0102

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 341, 249, 526, 714, 962, 684, 820, 944, 464, 7, 11, 259, 21, 261, 57, 73, 81, 321, 14, 518, 74, 522, 706, 322, 770, 44, 524, 52, 276, 548, 772, 168, 200, 648, 176, 816, 208, 336, 400, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_341, vertices_249, vertices_526, vertices_714, vertices_962, vertices_684, vertices_820, vertices_944, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_74, vertices_522, vertices_706, vertices_322, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_200, vertices_648, vertices_176, vertices_816, vertices_208, vertices_336, vertices_400, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_341), (false, vertices_249), (true, vertices_522), (true, vertices_706), (true, vertices_524), (true, vertices_548), (true, vertices_648), (true, vertices_816), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 14 16 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_341) then 10 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_706) then 13 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_400) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 8 706
cert_row_2 1 3 4 7 8 816
cert_row_4 2 1 2 4 6 8 684 44 3
cert_rows_3
cert_pivot_3 3 0 1
cert_heightProof 3
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 706 962 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 52 820 3
cert_coverFacet 5 944
cert_cover_5 5 1 3 4 6 7 176 944 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0102

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_multi_six_0103.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0103

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 341, 249, 654, 458, 898, 684, 820, 688, 976, 7, 11, 259, 21, 261, 57, 73, 81, 321, 14, 518, 330, 138, 386, 642, 770, 44, 652, 52, 276, 548, 772, 168, 200, 176, 560, 208, 336, 656, 784, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_341, vertices_249, vertices_654, vertices_458, vertices_898, vertices_684, vertices_820, vertices_688, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_330, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_200, vertices_176, vertices_560, vertices_208, vertices_336, vertices_656, vertices_784, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_341), (false, vertices_249), (true, vertices_138), (true, vertices_386), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_560), (true, vertices_656), (true, vertices_784), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_249) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_652) then 15 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 7 330
cert_row_2 1 1 2 6 8 652
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 330 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 688
cert_cover_2 5 4 3 6 8 176 688 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0103

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_multi_six_0104.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0104

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 398, 962, 940, 820, 232, 752, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 194, 322, 386, 44, 396, 52, 276, 804, 104, 168, 200, 112, 560, 592, 784, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_398, vertices_962, vertices_940, vertices_820, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_276, vertices_804, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_386), (true, vertices_396), (true, vertices_804), (true, vertices_168), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_396) then 12 else
  if p.val = (true, vertices_804) then 13 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_224) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 2 4 6 7 940 44 3
cert_row_4 2 1 2 4 6 8 940 44 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover 0 2 2 0 1 3 1 6 4 14 398 396 44 940 6
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 940
cert_cover_2 2 2 1 4 6 44 940 3
cert_coverFacet 3 820
cert_cover 3 4 2 1 3 3 1 7 4 52 820 804 44 940 6
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0104

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_multi_six_0105.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0105

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 910, 962, 684, 820, 232, 752, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 194, 322, 898, 44, 652, 52, 276, 548, 772, 104, 168, 200, 112, 560, 592, 784, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_910, vertices_962, vertices_684, vertices_820, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_898, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_898), (true, vertices_652), (true, vertices_548), (true, vertices_772), (true, vertices_168), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 9 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_898) then 13 else
  if p.val = (true, vertices_652) then 10 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_704) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 3 4 5 6 8 752 112 3
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 0 1 2 6 7 910 14 3
cert_row_4 3 0 1 2 6 8 910 14 3
cert_rows
cert_pivot_2 5 3 7 1
cert_heightProof 4
cert_coverFacet 0 910
cert_cover_2 0 1 0 2 6 14 910 3
cert_coverFacet 1 962
cert_cover 1 6 1 0 5 3 0 7 2 194 962 898 14 910 6
cert_coverFacet 2 684
cert_cover 2 4 1 1 2 3 0 6 2 44 684 652 14 910 6
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 752
cert_cover_5 5 0 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0105

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_multi_six_0106.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0106

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 297, 225, 929, 334, 962, 860, 824, 752, 7, 11, 131, 53, 69, 41, 265, 97, 161, 289, 193, 385, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 792, 296, 112, 560, 592, 224, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_297, vertices_225, vertices_929, vertices_334, vertices_962, vertices_860, vertices_824, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_161, vertices_289, vertices_193, vertices_385, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_792, vertices_296, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_297), (false, vertices_225), (false, vertices_929), (true, vertices_322), (true, vertices_332), (true, vertices_792), (true, vertices_560), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 14 16 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 8 else
  if p.val = (false, vertices_395) then 9 else
  if p.val = (false, vertices_117) then 12 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (false, vertices_929) then 18 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_332) then 13 else
  if p.val = (true, vertices_792) then 15 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_704) then 5 else
  if p.val = (true, vertices_832) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 2 3 5 7 860 28 3
cert_row_4 2 1 2 3 5 8 860 28 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover 0 2 2 0 1 3 1 5 3 14 334 332 28 860 5
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 860
cert_cover_2 2 2 1 3 5 28 860 3
cert_coverFacet 3 824
cert_cover 3 4 2 2 3 3 1 7 3 56 824 792 28 860 5
cert_coverFacet 4 752
cert_cover_5 4 3 3 4 5 6 112 752 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0106

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_multi_six_0107.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0107

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 117, 553, 225, 929, 846, 962, 348, 824, 496, 7, 11, 131, 53, 69, 41, 521, 97, 161, 545, 193, 641, 14, 70, 522, 194, 834, 642, 28, 332, 84, 56, 280, 552, 776, 112, 304, 336, 224, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_117, vertices_553, vertices_225, vertices_929, vertices_846, vertices_962, vertices_348, vertices_824, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_641, vertices_14, vertices_70, vertices_522, vertices_194, vertices_834, vertices_642, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_552, vertices_776, vertices_112, vertices_304, vertices_336, vertices_224, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_117), (false, vertices_553), (false, vertices_225), (false, vertices_929), (true, vertices_834), (true, vertices_332), (true, vertices_280), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 7 16 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_651) then 8 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (false, vertices_929) then 18 else
  if p.val = (true, vertices_834) then 12 else
  if p.val = (true, vertices_332) then 9 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_448) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inl 2
  | 8 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 3 4 5 6 7 496 112 3
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_4 2 0 1 2 5 7 846 14 3
cert_row_4 3 0 1 2 5 8 846 14 3
cert_rows
cert_pivot_2 6 3 7 0
cert_heightProof 4
cert_coverFacet 0 846
cert_cover_2 0 1 0 2 5 14 846 3
cert_coverFacet 1 962
cert_cover 1 6 1 0 5 3 0 7 2 194 962 834 14 846 5
cert_coverFacet 2 348
cert_cover 2 3 1 1 2 3 0 5 2 28 348 332 14 846 5
cert_coverFacet 3 824
cert_cover_5 3 1 2 3 4 7 56 824 3
cert_coverFacet 4 496
cert_cover_5 4 0 3 4 5 6 112 496 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0107

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_multi_six_0108.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0108

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 963, 117, 361, 654, 540, 212, 916, 824, 496, 7, 11, 195, 771, 53, 69, 41, 265, 97, 321, 14, 134, 522, 642, 28, 524, 84, 148, 532, 196, 644, 56, 536, 296, 776, 112, 304, 208, 400, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_963, vertices_117, vertices_361, vertices_654, vertices_540, vertices_212, vertices_916, vertices_824, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_771, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_522, vertices_642, vertices_28, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_963), (false, vertices_117), (false, vertices_361), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 9 11 17 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_963) then 20 else
  if p.val = (false, vertices_117) then 10 else
  if p.val = (false, vertices_361) then 13 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_148) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_784) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_963), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 540
cert_cover_2 1 2 1 3 8 28 540 3
cert_coverFacet 2 212
cert_cover_2 2 3 1 5 6 84 212 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 148 916 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0108

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_multi_six_0109.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0109

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 331, 781, 961, 86, 250, 300, 820, 724, 488, 944, 7, 11, 67, 13, 517, 265, 321, 577, 769, 22, 70, 58, 74, 82, 44, 268, 52, 84, 532, 292, 580, 772, 232, 296, 328, 176, 816, 208, 656, 416, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_331, vertices_781, vertices_961, vertices_86, vertices_250, vertices_300, vertices_820, vertices_724, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_265, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_58, vertices_74, vertices_82, vertices_44, vertices_268, vertices_52, vertices_84, vertices_532, vertices_292, vertices_580, vertices_772, vertices_232, vertices_296, vertices_328, vertices_176, vertices_816, vertices_208, vertices_656, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_331), (false, vertices_781), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_532), (true, vertices_292), (true, vertices_232), (true, vertices_296), (true, vertices_176), (true, vertices_816), (true, vertices_208), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_232) then 16 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
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
cert_row_4 1 0 2 3 5 4 250 58 3
cert_row_4 2 0 2 3 5 6 250 58 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 250
cert_cover_2 1 2 0 3 5 58 250 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 84 724 3
cert_coverFacet 5 488
cert_cover 5 5 2 2 4 3 0 7 3 232 488 232 58 250 5
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0109

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_multi_six_0110.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0110

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 245, 809, 481, 590, 962, 92, 568, 728, 944, 7, 11, 259, 53, 69, 41, 777, 225, 289, 321, 14, 70, 522, 322, 578, 770, 28, 76, 84, 56, 88, 536, 552, 584, 176, 560, 208, 656, 416, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_245, vertices_809, vertices_481, vertices_590, vertices_962, vertices_92, vertices_568, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_69, vertices_41, vertices_777, vertices_225, vertices_289, vertices_321, vertices_14, vertices_70, vertices_522, vertices_322, vertices_578, vertices_770, vertices_28, vertices_76, vertices_84, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_176, vertices_560, vertices_208, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_245), (false, vertices_809), (false, vertices_481), (true, vertices_578), (true, vertices_76), (true, vertices_88), (true, vertices_536), (true, vertices_584), (true, vertices_560), (true, vertices_656), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 13 16 17 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_245) then 18 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_481) then 19 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_88) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_245), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 322 962 2
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 728
cert_cover_5 4 2 2 3 5 6 88 728 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0110

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_multi_six_0111.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0111

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 341, 249, 654, 202, 962, 684, 820, 496, 928, 7, 11, 259, 21, 261, 57, 73, 81, 321, 14, 518, 74, 138, 194, 322, 642, 770, 44, 652, 52, 276, 548, 772, 168, 200, 240, 304, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_341, vertices_249, vertices_654, vertices_202, vertices_962, vertices_684, vertices_820, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_74, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_200, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_341), (false, vertices_249), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_652) then 15 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
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
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 3 4 5 6 240
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 0 5 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 496
cert_cover_5 5 2 3 4 5 7 240 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0111

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_multi_six_0112.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0112

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 341, 249, 526, 714, 962, 684, 820, 496, 928, 7, 11, 259, 21, 261, 57, 73, 81, 321, 14, 518, 74, 522, 706, 322, 770, 44, 524, 52, 276, 548, 772, 168, 200, 648, 240, 304, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_341, vertices_249, vertices_526, vertices_714, vertices_962, vertices_684, vertices_820, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_74, vertices_522, vertices_706, vertices_322, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_200, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_341), (false, vertices_249), (true, vertices_522), (true, vertices_706), (true, vertices_524), (true, vertices_548), (true, vertices_648), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_706) then 15 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
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
cert_row_2 0 0 5 6 8 706
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 0 5 2 1
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 706 962 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 496
cert_cover_5 5 1 3 4 5 7 240 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0112

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_multi_six_0113.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0113

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 341, 681, 817, 590, 962, 252, 712, 496, 928, 7, 11, 259, 21, 325, 41, 521, 49, 273, 545, 769, 14, 70, 522, 322, 578, 770, 60, 76, 84, 168, 200, 584, 648, 240, 304, 336, 416, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_341, vertices_681, vertices_817, vertices_590, vertices_962, vertices_252, vertices_712, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_325, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_522, vertices_322, vertices_578, vertices_770, vertices_60, vertices_76, vertices_84, vertices_168, vertices_200, vertices_584, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_341), (false, vertices_681), (false, vertices_817), (true, vertices_578), (true, vertices_76), (true, vertices_200), (true, vertices_584), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 14 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_779) then 9 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_681) then 15 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_200) then 2 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 322 2
cert_row_4 1 0 1 2 5 8 590 14 3
cert_row_4 2 1 2 3 5 4 252 60 3
cert_row_4 3 1 2 3 5 6 252 60 3
cert_rows
cert_pivot_2 7 0 4 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 14 590 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 322 962 2
cert_coverFacet 2 252
cert_cover_2 2 2 1 3 5 60 252 3
cert_coverFacet 3 712
cert_cover_2 3 5 2 6 8 200 712 3
cert_coverFacet 4 496
cert_cover 4 5 2 3 4 3 1 7 3 240 496 240 60 252 5
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0113

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0600 : Certifies 600 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0083.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0601 : Certifies 601 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0084.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0602 : Certifies 602 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0086.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0603 : Certifies 603 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0087.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0604 : Certifies 604 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0088.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0605 : Certifies 605 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0089.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0606 : Certifies 606 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0090.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0607 : Certifies 607 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0091.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0608 : Certifies 608 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0092.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0609 : Certifies 609 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0093.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0610 : Certifies 610 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0094.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0611 : Certifies 611 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0095.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0612 : Certifies 612 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0096.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0613 : Certifies 613 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0097.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0614 : Certifies 614 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0098.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0615 : Certifies 615 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0099.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0616 : Certifies 616 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0100.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0617 : Certifies 617 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0101.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0618 : Certifies 618 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0102.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0619 : Certifies 619 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0103.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0620 : Certifies 620 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0104.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0621 : Certifies 621 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0105.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0622 : Certifies 622 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0106.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0623 : Certifies 623 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0107.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0624 : Certifies 624 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0108.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0625 : Certifies 625 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0109.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0626 : Certifies 626 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0110.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0627 : Certifies 627 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0111.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0628 : Certifies 628 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0112.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0629 : Certifies 629 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0113.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B020 (j : Fin 30) :
    Certifies (600 + j.val) := by
  fin_cases j
  · exact projection_0600
  · exact projection_0601
  · exact projection_0602
  · exact projection_0603
  · exact projection_0604
  · exact projection_0605
  · exact projection_0606
  · exact projection_0607
  · exact projection_0608
  · exact projection_0609
  · exact projection_0610
  · exact projection_0611
  · exact projection_0612
  · exact projection_0613
  · exact projection_0614
  · exact projection_0615
  · exact projection_0616
  · exact projection_0617
  · exact projection_0618
  · exact projection_0619
  · exact projection_0620
  · exact projection_0621
  · exact projection_0622
  · exact projection_0623
  · exact projection_0624
  · exact projection_0625
  · exact projection_0626
  · exact projection_0627
  · exact projection_0628
  · exact projection_0629

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
