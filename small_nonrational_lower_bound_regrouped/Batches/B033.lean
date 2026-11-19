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
/- Source: ProjectionCertificates/R_one_six_0424.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0424

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 325, 233, 369, 782, 454, 906, 540, 696, 240, 976, 7, 11, 67, 21, 69, 261, 41, 201, 49, 273, 97, 321, 14, 70, 262, 138, 778, 194, 386, 28, 524, 532, 324, 772, 56, 536, 168, 648, 112, 176, 208, 336, 656, 784, 224, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_325, vertices_233, vertices_369, vertices_782, vertices_454, vertices_906, vertices_540, vertices_696, vertices_240, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_261, vertices_41, vertices_201, vertices_49, vertices_273, vertices_97, vertices_321, vertices_14, vertices_70, vertices_262, vertices_138, vertices_778, vertices_194, vertices_386, vertices_28, vertices_524, vertices_532, vertices_324, vertices_772, vertices_56, vertices_536, vertices_168, vertices_648, vertices_112, vertices_176, vertices_208, vertices_336, vertices_656, vertices_784, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_325), (false, vertices_233), (false, vertices_369), (true, vertices_262), (true, vertices_778), (true, vertices_386), (true, vertices_524), (true, vertices_536), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 19 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 20 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_369) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 0 2 7 8 778
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 906
cert_cover_5 2 1 0 2 6 7 138 906 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 240
cert_cover_2 5 4 3 5 6 112 240 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0424

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0425.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0425

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 451, 589, 833, 897, 342, 410, 684, 628, 440, 880, 928, 7, 11, 67, 131, 13, 69, 521, 321, 577, 385, 641, 769, 22, 70, 26, 138, 274, 322, 386, 44, 524, 52, 84, 548, 580, 56, 408, 168, 648, 624, 304, 336, 416, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_451, vertices_589, vertices_833, vertices_897, vertices_342, vertices_410, vertices_684, vertices_628, vertices_440, vertices_880, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_13, vertices_69, vertices_521, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_138, vertices_274, vertices_322, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_408, vertices_168, vertices_648, vertices_624, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_451), (false, vertices_589), (false, vertices_833), (false, vertices_897), (true, vertices_274), (true, vertices_84), (true, vertices_548), (true, vertices_408), (true, vertices_168), (true, vertices_624), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (false, vertices_897) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_408) then 19 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_624) then 21 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_2 1 2 3 6 7 408
cert_row_2 2 3 4 5 8 624
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 0 7 3 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 26 410 3
cert_coverFacet 2 684
cert_cover_5 2 3 1 2 4 6 44 684 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 880
cert_cover_5 5 2 3 4 5 7 624 880 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0425

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0426.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0426

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 597, 537, 961, 206, 394, 428, 244, 824, 944, 720, 7, 11, 67, 259, 21, 69, 25, 521, 529, 449, 577, 769, 14, 70, 138, 266, 194, 386, 44, 140, 52, 84, 164, 196, 56, 536, 296, 392, 776, 176, 816, 208, 592, 656, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_597, vertices_537, vertices_961, vertices_206, vertices_394, vertices_428, vertices_244, vertices_824, vertices_944, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_521, vertices_529, vertices_449, vertices_577, vertices_769, vertices_14, vertices_70, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_536, vertices_296, vertices_392, vertices_776, vertices_176, vertices_816, vertices_208, vertices_592, vertices_656, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_597), (false, vertices_537), (false, vertices_961), (true, vertices_138), (true, vertices_140), (true, vertices_164), (true, vertices_196), (true, vertices_296), (true, vertices_392), (true, vertices_176), (true, vertices_816), (true, vertices_208), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 18 20 21 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_451) then 22 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_816) then 19 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 8 0 2 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 244
cert_cover_5 3 3 1 3 4 5 52 244 3
cert_coverFacet 4 824
cert_cover_5 4 0 2 3 4 7 56 824 3
cert_coverFacet 5 944
cert_cover_5 5 0 3 4 6 7 176 944 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0426

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0427.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0427

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 597, 537, 961, 206, 394, 428, 244, 824, 752, 928, 7, 11, 67, 259, 21, 69, 25, 521, 529, 449, 577, 769, 14, 70, 138, 266, 194, 386, 44, 140, 52, 84, 164, 196, 56, 536, 296, 392, 776, 240, 560, 592, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_597, vertices_537, vertices_961, vertices_206, vertices_394, vertices_428, vertices_244, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_521, vertices_529, vertices_449, vertices_577, vertices_769, vertices_14, vertices_70, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_536, vertices_296, vertices_392, vertices_776, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_597), (false, vertices_537), (false, vertices_961), (true, vertices_138), (true, vertices_140), (true, vertices_164), (true, vertices_196), (true, vertices_296), (true, vertices_392), (true, vertices_240), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 18 20 21 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_451) then 22 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 752
cert_cover_5 5 1 3 4 5 8 240 752 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0427

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0428.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0428

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 85, 601, 961, 398, 198, 300, 244, 932, 824, 752, 7, 11, 67, 259, 21, 69, 25, 521, 81, 449, 577, 769, 14, 70, 134, 266, 194, 386, 44, 268, 52, 84, 164, 292, 196, 388, 56, 536, 296, 776, 240, 560, 592, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_85, vertices_601, vertices_961, vertices_398, vertices_198, vertices_300, vertices_244, vertices_932, vertices_824, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_521, vertices_81, vertices_449, vertices_577, vertices_769, vertices_14, vertices_70, vertices_134, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_56, vertices_536, vertices_296, vertices_776, vertices_240, vertices_560, vertices_592, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_85), (false, vertices_601), (false, vertices_961), (true, vertices_134), (true, vertices_268), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 16 18 20 21 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_451) then 22 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_601) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_4 2 1 4 6 7 8 932 164 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 244
cert_cover_5 3 0 1 3 4 5 52 244 3
cert_coverFacet 4 932
cert_cover_5 4 2 1 4 6 7 164 932 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 752
cert_cover_5 6 0 3 4 5 8 240 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0428

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0430.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0430

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 213, 409, 78, 586, 962, 620, 436, 932, 708, 824, 7, 11, 67, 259, 21, 69, 25, 265, 145, 193, 385, 14, 70, 74, 522, 450, 578, 770, 44, 76, 52, 148, 420, 548, 196, 580, 644, 56, 280, 552, 584, 776, 304, 400, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_213, vertices_409, vertices_78, vertices_586, vertices_962, vertices_620, vertices_436, vertices_932, vertices_708, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_74, vertices_522, vertices_450, vertices_578, vertices_770, vertices_44, vertices_76, vertices_52, vertices_148, vertices_420, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_552, vertices_584, vertices_776, vertices_304, vertices_400, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_409), (true, vertices_74), (true, vertices_578), (true, vertices_76), (true, vertices_420), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_420) then 19 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 0 71 1 74 578 76 548 580 644 552 584 304 800 704 896 779 451 213 420 409
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 7 450
cert_row_2 1 1 4 6 7 420
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 8 450 962 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 44 620 3
cert_coverFacet 4 436
cert_cover_5 4 1 1 3 4 6 52 436 3
cert_coverFacet 5 932
cert_cover_5 5 1 1 4 6 8 420 932 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0430

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0431.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0431

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 213, 409, 78, 586, 962, 620, 436, 740, 824, 928, 7, 11, 67, 259, 21, 69, 25, 265, 145, 193, 385, 14, 70, 74, 522, 450, 578, 770, 44, 76, 52, 148, 612, 164, 196, 56, 280, 552, 584, 776, 304, 400, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_213, vertices_409, vertices_78, vertices_586, vertices_962, vertices_620, vertices_436, vertices_740, vertices_824, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_74, vertices_522, vertices_450, vertices_578, vertices_770, vertices_44, vertices_76, vertices_52, vertices_148, vertices_612, vertices_164, vertices_196, vertices_56, vertices_280, vertices_552, vertices_584, vertices_776, vertices_304, vertices_400, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_409), (true, vertices_74), (true, vertices_578), (true, vertices_76), (true, vertices_612), (true, vertices_164), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_612) then 19 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 0 71 1 74 578 76 164 552 584 304 416 672 800 704 896 779 451 213 612 409
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 7 450
cert_row_2 1 1 4 5 8 612
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 8 450 962 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 44 620 3
cert_coverFacet 4 436
cert_cover_5 4 2 1 3 4 6 52 436 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 612 740 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0431

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0432.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0432

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 406, 198, 282, 108, 244, 824, 744, 944, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 134, 26, 266, 274, 194, 386, 44, 76, 52, 148, 100, 196, 56, 280, 104, 552, 584, 776, 176, 816, 400, 224, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_406, vertices_198, vertices_282, vertices_108, vertices_244, vertices_824, vertices_744, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_134, vertices_26, vertices_266, vertices_274, vertices_194, vertices_386, vertices_44, vertices_76, vertices_52, vertices_148, vertices_100, vertices_196, vertices_56, vertices_280, vertices_104, vertices_552, vertices_584, vertices_776, vertices_176, vertices_816, vertices_400, vertices_224, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_134), (true, vertices_274), (true, vertices_148), (true, vertices_100), (true, vertices_196), (true, vertices_280), (true, vertices_104), (true, vertices_552), (true, vertices_176), (true, vertices_816), (true, vertices_400), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 19 21 22 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_816) then 20 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 22 3
cert_row_2 1 3 4 7 8 816
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 22 406 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0432

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0433.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0433

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 282, 402, 236, 436, 824, 744, 928, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 266, 146, 274, 194, 386, 44, 76, 52, 148, 164, 196, 56, 280, 232, 552, 584, 776, 304, 400, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_282, vertices_402, vertices_236, vertices_436, vertices_824, vertices_744, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_274, vertices_194, vertices_386, vertices_44, vertices_76, vertices_52, vertices_148, vertices_164, vertices_196, vertices_56, vertices_280, vertices_232, vertices_552, vertices_584, vertices_776, vertices_304, vertices_400, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_146), (true, vertices_274), (true, vertices_148), (true, vertices_164), (true, vertices_196), (true, vertices_280), (true, vertices_232), (true, vertices_552), (true, vertices_304), (true, vertices_400), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 21 22 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_232) then 19 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 2 4 5 6 232
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 236
cert_cover_5 3 1 1 2 4 5 44 236 3
cert_coverFacet 4 436
cert_cover_5 4 2 1 3 4 6 52 436 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 744
cert_cover_5 6 1 2 4 5 8 232 744 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0433

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0434.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0434

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 154, 394, 812, 628, 440, 944, 720, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 138, 266, 146, 194, 386, 44, 524, 52, 84, 548, 580, 56, 152, 296, 392, 776, 432, 560, 208, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_154, vertices_394, vertices_812, vertices_628, vertices_440, vertices_944, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_138, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_152, vertices_296, vertices_392, vertices_776, vertices_432, vertices_560, vertices_208, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_138), (true, vertices_146), (true, vertices_84), (true, vertices_548), (true, vertices_152), (true, vertices_296), (true, vertices_392), (true, vertices_432), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 19 21 22 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_432) then 20 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 628
cert_cover_5 4 3 1 3 4 5 52 628 3
cert_coverFacet 5 440
cert_cover_5 5 1 2 3 4 6 56 440 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 8 432 944 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0434

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0435.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0435

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 154, 394, 812, 628, 440, 752, 928, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 138, 266, 146, 194, 386, 44, 524, 52, 84, 548, 580, 56, 152, 296, 392, 776, 624, 176, 208, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_154, vertices_394, vertices_812, vertices_628, vertices_440, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_138, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_152, vertices_296, vertices_392, vertices_776, vertices_624, vertices_176, vertices_208, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_138), (true, vertices_146), (true, vertices_84), (true, vertices_548), (true, vertices_152), (true, vertices_296), (true, vertices_392), (true, vertices_624), (true, vertices_176), (true, vertices_208), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 19 21 22 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_624) then 20 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 3 4 5 8 624
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 52 628 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 56 440 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 6 624 752 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0435

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0436.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0436

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 282, 402, 812, 628, 440, 752, 928, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 266, 146, 274, 194, 386, 44, 524, 52, 84, 548, 580, 56, 280, 296, 776, 624, 176, 208, 400, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_282, vertices_402, vertices_812, vertices_628, vertices_440, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_274, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_280, vertices_296, vertices_776, vertices_624, vertices_176, vertices_208, vertices_400, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_146), (true, vertices_274), (true, vertices_84), (true, vertices_548), (true, vertices_280), (true, vertices_296), (true, vertices_624), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 19 21 22 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_624) then 20 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 3 4 5 8 624
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 52 628 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 56 440 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 6 624 752 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0436

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0437.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0437

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 410, 812, 116, 612, 312, 752, 944, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 84, 100, 548, 580, 56, 280, 296, 776, 112, 688, 304, 208, 400, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_410, vertices_812, vertices_116, vertices_612, vertices_312, vertices_752, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_100, vertices_548, vertices_580, vertices_56, vertices_280, vertices_296, vertices_776, vertices_112, vertices_688, vertices_304, vertices_208, vertices_400, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_146), (true, vertices_84), (true, vertices_100), (true, vertices_548), (true, vertices_280), (true, vertices_296), (true, vertices_112), (true, vertices_688), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 19 21 22 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_688) then 20 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_4 1 0 2 3 6 7 410 26 3
cert_row_2 2 3 4 6 8 688
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 5 0 3 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 26 410 3
cert_coverFacet 2 812
cert_cover_5 2 3 1 2 4 7 44 812 3
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 612
cert_cover_2 4 4 1 5 8 100 612 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 752
cert_cover_5 6 2 3 4 5 6 112 752 3
cert_coverFacet 7 944
cert_cover_5 7 2 3 4 6 7 688 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0437

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0438.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0438

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 213, 409, 590, 962, 812, 628, 184, 424, 752, 928, 7, 11, 67, 259, 21, 69, 25, 265, 145, 193, 385, 14, 70, 522, 450, 578, 770, 44, 524, 52, 84, 548, 580, 56, 152, 168, 296, 392, 776, 624, 176, 208, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_213, vertices_409, vertices_590, vertices_962, vertices_812, vertices_628, vertices_184, vertices_424, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_522, vertices_450, vertices_578, vertices_770, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_152, vertices_168, vertices_296, vertices_392, vertices_776, vertices_624, vertices_176, vertices_208, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_409), (true, vertices_578), (true, vertices_524), (true, vertices_548), (true, vertices_580), (true, vertices_168), (true, vertices_296), (true, vertices_624), (true, vertices_176), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_624) then 22 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 8 624
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 1 2 5 8 590 14 3
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 14 590 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 8 450 962 3
cert_coverFacet 2 812
cert_cover_5 2 3 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 52 628 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 752
cert_cover_5 6 0 3 4 5 6 624 752 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0438

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0439.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0439

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 410, 812, 628, 440, 688, 720, 928, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 84, 548, 580, 56, 408, 296, 776, 176, 560, 208, 592, 656, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_410, vertices_812, vertices_628, vertices_440, vertices_688, vertices_720, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_560, vertices_208, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_146), (true, vertices_84), (true, vertices_548), (true, vertices_408), (true, vertices_296), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 21 22 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_408) then 19 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 2 3 6 7 408
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 26 410 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 3 1 3 4 5 52 628 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 688
cert_cover_2 5 4 3 6 8 176 688 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0439

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0440.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0440

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 410, 812, 628, 440, 240, 736, 928, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 84, 548, 580, 56, 408, 296, 776, 112, 176, 208, 224, 608, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_410, vertices_812, vertices_628, vertices_440, vertices_240, vertices_736, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_408, vertices_296, vertices_776, vertices_112, vertices_176, vertices_208, vertices_224, vertices_608, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_146), (true, vertices_84), (true, vertices_548), (true, vertices_408), (true, vertices_296), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_224), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 21 22 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 23 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_408) then 19 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 2 3 6 7 408
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 26 410 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 3 1 3 4 5 52 628 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 240
cert_cover_2 5 4 3 5 6 112 240 3
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0440

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0441.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0441

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 213, 409, 590, 962, 620, 436, 228, 824, 736, 928, 7, 11, 67, 259, 21, 69, 25, 265, 145, 193, 385, 14, 70, 522, 450, 578, 770, 44, 588, 52, 148, 100, 164, 196, 56, 280, 552, 776, 304, 400, 224, 608, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_213, vertices_409, vertices_590, vertices_962, vertices_620, vertices_436, vertices_228, vertices_824, vertices_736, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_522, vertices_450, vertices_578, vertices_770, vertices_44, vertices_588, vertices_52, vertices_148, vertices_100, vertices_164, vertices_196, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_409), (true, vertices_578), (true, vertices_588), (true, vertices_100), (true, vertices_164), (true, vertices_552), (true, vertices_304), (true, vertices_224), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_588) then 19 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 0 71 1 578 100 164 552 304 224 608 416 672 800 704 896 779 451 213 588 409
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 7 450
cert_row_2 1 1 2 5 8 588
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 14 590 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 8 450 962 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 52 436 3
cert_coverFacet 4 228
cert_cover_2 4 4 1 5 6 100 228 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0441

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0443.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0443

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 597, 809, 689, 398, 454, 330, 156, 724, 440, 840, 992, 7, 11, 67, 21, 69, 41, 521, 49, 529, 545, 577, 14, 70, 390, 74, 266, 322, 28, 140, 596, 148, 196, 56, 152, 296, 328, 584, 392, 776, 176, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_597, vertices_809, vertices_689, vertices_398, vertices_454, vertices_330, vertices_156, vertices_724, vertices_440, vertices_840, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_529, vertices_545, vertices_577, vertices_14, vertices_70, vertices_390, vertices_74, vertices_266, vertices_322, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_597), (false, vertices_809), (false, vertices_689), (true, vertices_390), (true, vertices_266), (true, vertices_322), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_328), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_390) then 15 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 71 266 322 140 148 196 152 328 392 416 448 704 832 587 390 63 597 809 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 6 596 724 3
cert_coverFacet 5 440
cert_cover_5 5 2 2 3 4 6 56 440 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0443

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0444.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0444

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 587, 323, 149, 553, 433, 865, 78, 454, 668, 716, 824, 976, 7, 11, 67, 259, 21, 133, 41, 521, 49, 145, 289, 545, 321, 577, 385, 14, 70, 390, 74, 322, 28, 76, 652, 148, 196, 56, 536, 552, 584, 304, 400, 656, 784, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_587, vertices_323, vertices_149, vertices_553, vertices_433, vertices_865, vertices_78, vertices_454, vertices_668, vertices_716, vertices_824, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_14, vertices_70, vertices_390, vertices_74, vertices_322, vertices_28, vertices_76, vertices_652, vertices_148, vertices_196, vertices_56, vertices_536, vertices_552, vertices_584, vertices_304, vertices_400, vertices_656, vertices_784, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_587), (false, vertices_323), (false, vertices_149), (false, vertices_553), (false, vertices_433), (false, vertices_865), (true, vertices_70), (true, vertices_76), (true, vertices_652), (true, vertices_196), (true, vertices_536), (true, vertices_656), (true, vertices_784), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_553) then 2 else
  if p.val = (false, vertices_433) then 19 else
  if p.val = (false, vertices_865) then 21 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_652) then 16 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 1 2 6 8 652
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 5 6 7 8 976 400 1
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 76 716 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 400 976 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0444

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0445.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0445

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 579, 597, 425, 817, 398, 454, 834, 220, 248, 624, 992, 7, 11, 67, 515, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 390, 266, 322, 578, 770, 28, 140, 84, 196, 56, 216, 168, 392, 112, 560, 592, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_579, vertices_597, vertices_425, vertices_817, vertices_398, vertices_454, vertices_834, vertices_220, vertices_248, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_216, vertices_168, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_579), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_390), (true, vertices_322), (true, vertices_140), (true, vertices_196), (true, vertices_216), (true, vertices_112), (true, vertices_224), (true, vertices_608), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (true, vertices_390) then 12 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_216) then 18 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_2 1 0 1 6 7 390
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 0 2 4
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 28 220 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0445

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0446.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0446

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 579, 597, 809, 689, 398, 454, 834, 220, 440, 720, 992, 7, 11, 67, 515, 21, 69, 41, 777, 49, 529, 545, 577, 14, 70, 390, 266, 322, 578, 770, 28, 140, 84, 196, 56, 152, 296, 392, 176, 208, 592, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_579, vertices_597, vertices_809, vertices_689, vertices_398, vertices_454, vertices_834, vertices_220, vertices_440, vertices_720, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_777, vertices_49, vertices_529, vertices_545, vertices_577, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_176, vertices_208, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_579), (false, vertices_597), (false, vertices_809), (false, vertices_689), (true, vertices_390), (true, vertices_322), (true, vertices_140), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_208), (true, vertices_416), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_390) then 13 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 3 5 6 220 28 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 220
cert_cover_5 3 1 1 2 3 5 28 220 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 720
cert_cover_2 5 5 3 6 8 208 720 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0446

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0447.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0447

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 597, 809, 689, 398, 454, 778, 834, 156, 724, 440, 992, 7, 11, 67, 21, 69, 41, 521, 49, 529, 545, 577, 14, 70, 390, 266, 522, 322, 578, 770, 28, 140, 596, 148, 196, 56, 152, 296, 392, 776, 176, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_597, vertices_809, vertices_689, vertices_398, vertices_454, vertices_778, vertices_834, vertices_156, vertices_724, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_529, vertices_545, vertices_577, vertices_14, vertices_70, vertices_390, vertices_266, vertices_522, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_776, vertices_176, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_597), (false, vertices_809), (false, vertices_689), (true, vertices_390), (true, vertices_266), (true, vertices_322), (true, vertices_770), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_390) then 15 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
cert_nodeAtPriority_17 71 266 322 770 140 148 196 152 392 416 448 704 832 587 390 63 597 809 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 156
cert_cover_2 4 2 1 3 6 28 156 3
cert_coverFacet 5 724
cert_cover_5 5 1 1 3 5 6 596 724 3
cert_coverFacet 6 440
cert_cover_5 6 2 2 3 4 6 56 440 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0447

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0451.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0451

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 85, 425, 817, 593, 398, 454, 604, 716, 696, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 81, 529, 289, 577, 769, 14, 70, 390, 266, 322, 28, 588, 140, 84, 196, 56, 536, 168, 392, 648, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_85, vertices_425, vertices_817, vertices_593, vertices_398, vertices_454, vertices_604, vertices_716, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_81, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_588, vertices_140, vertices_84, vertices_196, vertices_56, vertices_536, vertices_168, vertices_392, vertices_648, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_85), (false, vertices_425), (false, vertices_817), (false, vertices_593), (true, vertices_390), (true, vertices_588), (true, vertices_140), (true, vertices_196), (true, vertices_536), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_85) then 2 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (false, vertices_593) then 3 else
  if p.val = (true, vertices_390) then 13 else
  if p.val = (true, vertices_588) then 16 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 3 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 1 2 5 8 588
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 604
cert_cover_5 2 1 1 2 3 5 28 604 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 588 716 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0451

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0453.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0453

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 425, 817, 398, 454, 92, 204, 696, 728, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 390, 266, 322, 28, 76, 140, 84, 196, 56, 88, 664, 168, 200, 392, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_425, vertices_817, vertices_398, vertices_454, vertices_92, vertices_204, vertices_696, vertices_728, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_76, vertices_140, vertices_84, vertices_196, vertices_56, vertices_88, vertices_664, vertices_168, vertices_200, vertices_392, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_390), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_88), (true, vertices_664), (true, vertices_200), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (true, vertices_390) then 12 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_664) then 18 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 8 664
cert_row_2 1 0 1 6 7 390
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 0 2 4
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 204
cert_cover_2 3 2 1 5 6 76 204 3
cert_coverFacet 4 696
cert_cover_5 4 0 2 3 4 6 56 696 3
cert_coverFacet 5 728
cert_cover_5 5 0 2 3 5 6 88 728 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0453

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0454.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0454

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 589, 85, 681, 241, 961, 78, 406, 454, 282, 842, 212, 824, 944, 13, 21, 69, 41, 521, 49, 81, 161, 193, 577, 641, 14, 22, 70, 390, 26, 74, 266, 274, 322, 76, 84, 148, 196, 56, 280, 552, 584, 776, 176, 816, 208, 400, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_589, vertices_85, vertices_681, vertices_241, vertices_961, vertices_78, vertices_406, vertices_454, vertices_282, vertices_842, vertices_212, vertices_824, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_161, vertices_193, vertices_577, vertices_641, vertices_14, vertices_22, vertices_70, vertices_390, vertices_26, vertices_74, vertices_266, vertices_274, vertices_322, vertices_76, vertices_84, vertices_148, vertices_196, vertices_56, vertices_280, vertices_552, vertices_584, vertices_776, vertices_176, vertices_816, vertices_208, vertices_400, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_589), (false, vertices_85), (false, vertices_681), (false, vertices_241), (false, vertices_961), (true, vertices_70), (true, vertices_390), (true, vertices_74), (true, vertices_266), (true, vertices_274), (true, vertices_322), (true, vertices_148), (true, vertices_196), (true, vertices_280), (true, vertices_776), (true, vertices_816), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_390) then 12 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_816) then 20 else
  if p.val = (true, vertices_400) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_2 1 0 1 6 7 390
cert_row_4 2 0 2 5 7 8 842 74 3
cert_rows_3
cert_pivot_3 1 3 0
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 406
cert_cover_5 1 1 0 1 3 6 22 406 3
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 6 70 454 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 842
cert_cover_5 4 2 0 2 5 7 74 842 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 824
cert_cover_5 6 0 2 3 4 7 56 824 3
cert_coverFacet 7 944
cert_cover_5 7 0 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0454

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0455.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0455

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 451, 597, 217, 270, 838, 428, 820, 632, 744, 928, 960, 7, 11, 67, 387, 21, 69, 25, 137, 81, 193, 14, 70, 262, 266, 322, 44, 268, 52, 532, 292, 580, 772, 56, 88, 616, 168, 200, 392, 560, 592, 416, 672, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_451, vertices_597, vertices_217, vertices_270, vertices_838, vertices_428, vertices_820, vertices_632, vertices_744, vertices_928, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_387, vertices_21, vertices_69, vertices_25, vertices_137, vertices_81, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_88, vertices_616, vertices_168, vertices_200, vertices_392, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_451), (false, vertices_597), (false, vertices_217), (true, vertices_262), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_616), (true, vertices_168), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_616) then 21 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_616), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 70 3
cert_row_2 1 2 4 5 8 616
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 0 5 2 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 632
cert_cover_5 4 1 2 3 4 5 56 632 3
cert_coverFacet 5 744
cert_cover_5 5 1 2 4 5 6 616 744 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0455

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0456.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0456

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 425, 817, 398, 454, 604, 204, 696, 712, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 390, 266, 322, 28, 76, 140, 596, 196, 56, 536, 168, 200, 584, 392, 648, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_425, vertices_817, vertices_398, vertices_454, vertices_604, vertices_204, vertices_696, vertices_712, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_76, vertices_140, vertices_596, vertices_196, vertices_56, vertices_536, vertices_168, vertices_200, vertices_584, vertices_392, vertices_648, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_390), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_390) then 14 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
cert_nodeAtPriority_67 0 71 1 267 76 140 196 536 200 584 648 672 448 704 835 390 63 597 425 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 604
cert_cover_5 2 1 1 2 3 5 28 604 3
cert_coverFacet 3 204
cert_cover_2 3 2 1 5 6 76 204 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0456

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0457.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0457

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 589, 85, 681, 241, 961, 78, 406, 454, 794, 842, 212, 568, 944, 13, 21, 69, 41, 521, 49, 81, 161, 193, 577, 641, 14, 22, 70, 390, 26, 74, 778, 274, 322, 76, 84, 148, 196, 56, 536, 552, 584, 176, 560, 208, 400, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_589, vertices_85, vertices_681, vertices_241, vertices_961, vertices_78, vertices_406, vertices_454, vertices_794, vertices_842, vertices_212, vertices_568, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_161, vertices_193, vertices_577, vertices_641, vertices_14, vertices_22, vertices_70, vertices_390, vertices_26, vertices_74, vertices_778, vertices_274, vertices_322, vertices_76, vertices_84, vertices_148, vertices_196, vertices_56, vertices_536, vertices_552, vertices_584, vertices_176, vertices_560, vertices_208, vertices_400, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_589), (false, vertices_85), (false, vertices_681), (false, vertices_241), (false, vertices_961), (true, vertices_70), (true, vertices_390), (true, vertices_74), (true, vertices_778), (true, vertices_274), (true, vertices_322), (true, vertices_148), (true, vertices_196), (true, vertices_536), (true, vertices_560), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 17 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_589) then 12 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_390) then 13 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_778) then 16 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_2 1 0 1 6 7 390
cert_row_4 2 3 4 6 7 8 944 176 3
cert_rows_3
cert_pivot_3 0 2 3
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 406
cert_cover_5 1 1 0 1 3 6 22 406 3
cert_coverFacet 2 454
cert_cover_5 2 1 0 1 5 6 70 454 3
cert_coverFacet 3 794
cert_cover_5 3 0 0 2 3 7 26 794 3
cert_coverFacet 4 842
cert_cover_5 4 0 0 2 5 7 74 842 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 944
cert_cover_5 7 2 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0457

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0458.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0458

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 451, 597, 217, 782, 838, 556, 692, 440, 808, 720, 992, 7, 11, 67, 387, 21, 69, 25, 137, 81, 193, 14, 70, 774, 266, 322, 44, 524, 52, 532, 548, 580, 56, 152, 296, 552, 392, 776, 176, 208, 592, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_451, vertices_597, vertices_217, vertices_782, vertices_838, vertices_556, vertices_692, vertices_440, vertices_808, vertices_720, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_387, vertices_21, vertices_69, vertices_25, vertices_137, vertices_81, vertices_193, vertices_14, vertices_70, vertices_774, vertices_266, vertices_322, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_580, vertices_56, vertices_152, vertices_296, vertices_552, vertices_392, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_451), (false, vertices_597), (false, vertices_217), (true, vertices_774), (true, vertices_524), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0458

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0459.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0459

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 75, 835, 149, 809, 585, 433, 78, 454, 604, 724, 696, 992, 7, 11, 67, 259, 21, 133, 41, 73, 521, 49, 145, 289, 577, 385, 769, 14, 70, 390, 74, 322, 28, 76, 596, 148, 196, 56, 536, 552, 584, 176, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_75, vertices_835, vertices_149, vertices_809, vertices_585, vertices_433, vertices_78, vertices_454, vertices_604, vertices_724, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_133, vertices_41, vertices_73, vertices_521, vertices_49, vertices_145, vertices_289, vertices_577, vertices_385, vertices_769, vertices_14, vertices_70, vertices_390, vertices_74, vertices_322, vertices_28, vertices_76, vertices_596, vertices_148, vertices_196, vertices_56, vertices_536, vertices_552, vertices_584, vertices_176, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_75), (false, vertices_835), (false, vertices_149), (false, vertices_809), (false, vertices_585), (false, vertices_433), (true, vertices_70), (true, vertices_76), (true, vertices_596), (true, vertices_196), (true, vertices_536), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_585) then 2 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_596) then 16 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 604
cert_cover_5 2 1 1 2 3 5 28 604 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 596 724 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0459

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0990 : Certifies 990 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0424.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0991 : Certifies 991 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0425.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0992 : Certifies 992 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0426.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0993 : Certifies 993 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0427.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0994 : Certifies 994 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0428.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0995 : Certifies 995 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0430.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0996 : Certifies 996 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0431.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0997 : Certifies 997 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0432.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0998 : Certifies 998 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0433.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0999 : Certifies 999 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0434.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1000 : Certifies 1000 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0435.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1001 : Certifies 1001 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0436.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1002 : Certifies 1002 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0437.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1003 : Certifies 1003 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0438.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1004 : Certifies 1004 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0439.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1005 : Certifies 1005 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0440.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1006 : Certifies 1006 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0441.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1007 : Certifies 1007 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0443.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1008 : Certifies 1008 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0444.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1009 : Certifies 1009 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0445.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1010 : Certifies 1010 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0446.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1011 : Certifies 1011 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0447.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1012 : Certifies 1012 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0451.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1013 : Certifies 1013 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0453.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1014 : Certifies 1014 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0454.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1015 : Certifies 1015 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0455.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1016 : Certifies 1016 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0456.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1017 : Certifies 1017 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0457.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1018 : Certifies 1018 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0458.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1019 : Certifies 1019 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0459.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B033 (j : Fin 30) :
    Certifies (990 + j.val) := by
  fin_cases j
  · exact projection_0990
  · exact projection_0991
  · exact projection_0992
  · exact projection_0993
  · exact projection_0994
  · exact projection_0995
  · exact projection_0996
  · exact projection_0997
  · exact projection_0998
  · exact projection_0999
  · exact projection_1000
  · exact projection_1001
  · exact projection_1002
  · exact projection_1003
  · exact projection_1004
  · exact projection_1005
  · exact projection_1006
  · exact projection_1007
  · exact projection_1008
  · exact projection_1009
  · exact projection_1010
  · exact projection_1011
  · exact projection_1012
  · exact projection_1013
  · exact projection_1014
  · exact projection_1015
  · exact projection_1016
  · exact projection_1017
  · exact projection_1018
  · exact projection_1019

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
