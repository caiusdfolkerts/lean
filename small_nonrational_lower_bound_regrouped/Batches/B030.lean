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
/- Source: ProjectionCertificates/R_one_six_0295.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0295

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 195, 387, 213, 409, 590, 962, 620, 436, 484, 824, 864, 7, 11, 67, 131, 259, 21, 69, 25, 265, 145, 193, 385, 14, 70, 522, 194, 578, 386, 770, 44, 588, 52, 148, 100, 420, 196, 56, 280, 552, 776, 304, 400, 352, 608, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_195, vertices_387, vertices_213, vertices_409, vertices_590, vertices_962, vertices_620, vertices_436, vertices_484, vertices_824, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_522, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_588, vertices_52, vertices_148, vertices_100, vertices_420, vertices_196, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_352, vertices_608, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_195), (false, vertices_387), (false, vertices_213), (false, vertices_409), (true, vertices_578), (true, vertices_588), (true, vertices_100), (true, vertices_420), (true, vertices_552), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 14 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_387) then 2 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_409) then 16 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_588) then 17 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_420) then 20 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_2 1 1 4 6 7 420
cert_row_2 2 1 2 5 8 588
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 2 0 1 2 5 14 590 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 620
cert_cover_5 2 2 1 2 4 5 44 620 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 484
cert_cover_5 4 1 1 4 5 6 100 484 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0295

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0296.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0296

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 809, 625, 782, 198, 390, 962, 412, 440, 240, 992, 7, 11, 67, 21, 69, 41, 521, 49, 81, 545, 577, 14, 70, 134, 262, 522, 194, 578, 386, 770, 28, 268, 148, 196, 388, 56, 408, 296, 776, 112, 176, 208, 224, 608, 416, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_809, vertices_625, vertices_782, vertices_198, vertices_390, vertices_962, vertices_412, vertices_440, vertices_240, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_70, vertices_134, vertices_262, vertices_522, vertices_194, vertices_578, vertices_386, vertices_770, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_112, vertices_176, vertices_208, vertices_224, vertices_608, vertices_416, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_809), (false, vertices_625), (true, vertices_134), (true, vertices_262), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_408), (true, vertices_176), (true, vertices_224), (true, vertices_416), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_408) then 18 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_960) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_2 1 5 6 7 8 960
cert_row_4 2 0 1 2 7 8 782 14 3
cert_rows_3
cert_pivot_3 5 3 0
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 412
cert_cover_5 4 0 1 2 3 6 28 412 3
cert_coverFacet 5 440
cert_cover_5 5 0 2 3 4 6 56 440 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0296

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0297.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0297

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 617, 433, 225, 782, 198, 390, 962, 412, 824, 992, 7, 11, 67, 21, 69, 41, 585, 49, 145, 97, 161, 193, 14, 70, 134, 262, 522, 194, 578, 386, 770, 28, 268, 148, 196, 388, 56, 280, 552, 776, 304, 400, 224, 608, 416, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_617, vertices_433, vertices_225, vertices_782, vertices_198, vertices_390, vertices_962, vertices_412, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_134, vertices_262, vertices_522, vertices_194, vertices_578, vertices_386, vertices_770, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_617), (false, vertices_433), (false, vertices_225), (true, vertices_134), (true, vertices_262), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_280), (true, vertices_776), (true, vertices_800), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 13 16 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_960) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 5 6 7 8 960
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 2 3 6 7 412 28 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 7 194 962 3
cert_coverFacet 4 412
cert_cover_5 4 2 1 2 3 6 28 412 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0297

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0299.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0299

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 341, 281, 961, 590, 714, 684, 628, 440, 880, 928, 7, 11, 67, 131, 21, 69, 25, 265, 273, 193, 321, 385, 14, 70, 586, 138, 194, 44, 524, 52, 84, 548, 580, 56, 280, 168, 392, 648, 624, 304, 336, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_341, vertices_281, vertices_961, vertices_590, vertices_714, vertices_684, vertices_628, vertices_440, vertices_880, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_25, vertices_265, vertices_273, vertices_193, vertices_321, vertices_385, vertices_14, vertices_70, vertices_586, vertices_138, vertices_194, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_280, vertices_168, vertices_392, vertices_648, vertices_624, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_341), (false, vertices_281), (false, vertices_961), (true, vertices_586), (true, vertices_524), (true, vertices_548), (true, vertices_580), (true, vertices_168), (true, vertices_648), (true, vertices_624), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 20 14 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_281) then 2 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_586) then 19 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_624) then 16 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_586), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 8 586
cert_row_2 1 3 4 5 8 624
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 586 714 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 52 628 3
cert_coverFacet 4 440
cert_cover_5 4 3 2 3 4 6 56 440 3
cert_coverFacet 5 880
cert_cover_5 5 1 3 4 5 7 624 880 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0299

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0300.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0300

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 587, 707, 277, 681, 433, 78, 198, 604, 852, 452, 824, 992, 7, 11, 579, 131, 21, 261, 41, 521, 49, 273, 161, 385, 641, 14, 70, 134, 74, 194, 28, 76, 596, 276, 196, 324, 388, 56, 536, 552, 584, 304, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_587, vertices_707, vertices_277, vertices_681, vertices_433, vertices_78, vertices_198, vertices_604, vertices_852, vertices_452, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_579, vertices_131, vertices_21, vertices_261, vertices_41, vertices_521, vertices_49, vertices_273, vertices_161, vertices_385, vertices_641, vertices_14, vertices_70, vertices_134, vertices_74, vertices_194, vertices_28, vertices_76, vertices_596, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_536, vertices_552, vertices_584, vertices_304, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_587), (false, vertices_707), (false, vertices_277), (false, vertices_681), (false, vertices_433), (true, vertices_70), (true, vertices_76), (true, vertices_596), (true, vertices_196), (true, vertices_324), (true, vertices_536), (true, vertices_784), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_596) then 12 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_2 0 1 3 5 8 596
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 2 1 4
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 604
cert_cover_5 2 0 1 2 3 5 28 604 3
cert_coverFacet 3 852
cert_cover_5 3 0 1 3 5 7 596 852 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0300

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0301.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0301

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 341, 281, 961, 590, 714, 684, 628, 440, 944, 848, 7, 11, 67, 131, 21, 69, 25, 265, 273, 193, 321, 385, 14, 70, 586, 138, 194, 44, 524, 52, 84, 548, 580, 56, 280, 168, 392, 648, 432, 560, 336, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_341, vertices_281, vertices_961, vertices_590, vertices_714, vertices_684, vertices_628, vertices_440, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_25, vertices_265, vertices_273, vertices_193, vertices_321, vertices_385, vertices_14, vertices_70, vertices_586, vertices_138, vertices_194, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_280, vertices_168, vertices_392, vertices_648, vertices_432, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_341), (false, vertices_281), (false, vertices_961), (true, vertices_586), (true, vertices_524), (true, vertices_548), (true, vertices_580), (true, vertices_168), (true, vertices_648), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 20 14 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_281) then 2 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_586) then 19 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_432) then 16 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_586), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 8 586
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 586 714 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 628
cert_cover_5 3 3 1 3 4 5 52 628 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 944
cert_cover_5 5 1 3 4 6 8 432 944 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0301

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0307.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0307

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 587, 835, 149, 809, 433, 78, 198, 450, 604, 724, 696, 992, 7, 11, 579, 259, 21, 133, 41, 521, 49, 145, 289, 385, 769, 14, 70, 134, 74, 194, 322, 386, 28, 76, 596, 148, 196, 56, 536, 552, 584, 176, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_587, vertices_835, vertices_149, vertices_809, vertices_433, vertices_78, vertices_198, vertices_450, vertices_604, vertices_724, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_579, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_289, vertices_385, vertices_769, vertices_14, vertices_70, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_28, vertices_76, vertices_596, vertices_148, vertices_196, vertices_56, vertices_536, vertices_552, vertices_584, vertices_176, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_587), (false, vertices_835), (false, vertices_149), (false, vertices_809), (false, vertices_433), (true, vertices_70), (true, vertices_194), (true, vertices_76), (true, vertices_596), (true, vertices_196), (true, vertices_536), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_596) then 12 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
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
cert_row_2 0 1 3 5 8 596
cert_row_4 1 2 3 4 6 8 696 56 3
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 2 1 4
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 5 28 604 3
cert_coverFacet 4 724
cert_cover_5 4 0 1 3 5 6 596 724 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0307

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0308.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0308

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 597, 217, 270, 710, 902, 300, 820, 632, 488, 992, 7, 11, 67, 131, 21, 69, 25, 137, 81, 193, 14, 70, 646, 262, 266, 194, 386, 44, 268, 52, 532, 292, 580, 772, 56, 88, 104, 296, 200, 392, 560, 592, 480, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_597, vertices_217, vertices_270, vertices_710, vertices_902, vertices_300, vertices_820, vertices_632, vertices_488, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_25, vertices_137, vertices_81, vertices_193, vertices_14, vertices_70, vertices_646, vertices_262, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_88, vertices_104, vertices_296, vertices_200, vertices_392, vertices_560, vertices_592, vertices_480, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_597), (false, vertices_217), (true, vertices_646), (true, vertices_262), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_104), (true, vertices_296), (true, vertices_560), (true, vertices_480), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (true, vertices_646) then 15 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_480) then 23 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_646), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_2 1 4 5 6 7 480
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 70 710 3
cert_coverFacet 2 902
cert_cover_5 2 0 0 1 6 7 646 902 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 488
cert_cover_5 6 1 2 4 5 6 104 488 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 8 480 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0308

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0309.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0309

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 333, 961, 662, 710, 154, 108, 628, 440, 872, 944, 7, 11, 67, 131, 13, 69, 265, 193, 321, 385, 22, 70, 646, 26, 138, 146, 194, 44, 76, 52, 532, 100, 580, 56, 152, 104, 296, 328, 392, 432, 560, 656, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_333, vertices_961, vertices_662, vertices_710, vertices_154, vertices_108, vertices_628, vertices_440, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_13, vertices_69, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_646, vertices_26, vertices_138, vertices_146, vertices_194, vertices_44, vertices_76, vertices_52, vertices_532, vertices_100, vertices_580, vertices_56, vertices_152, vertices_104, vertices_296, vertices_328, vertices_392, vertices_432, vertices_560, vertices_656, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_333), (false, vertices_961), (true, vertices_646), (true, vertices_146), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_152), (true, vertices_104), (true, vertices_296), (true, vertices_432), (true, vertices_560), (true, vertices_656), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_646) then 15 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_432) then 21 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_646), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 22 662 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 70 710 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 628
cert_cover_5 4 2 1 3 4 5 52 628 3
cert_coverFacet 5 440
cert_cover_5 5 1 2 3 4 6 56 440 3
cert_coverFacet 6 872
cert_cover_5 6 3 2 4 5 7 104 872 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 8 432 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0309

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0310.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0310

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 333, 961, 598, 154, 722, 620, 692, 440, 872, 928, 7, 11, 67, 131, 13, 69, 265, 193, 321, 385, 22, 70, 26, 138, 594, 146, 194, 44, 76, 52, 532, 548, 580, 56, 152, 616, 296, 328, 392, 176, 656, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_333, vertices_961, vertices_598, vertices_154, vertices_722, vertices_620, vertices_692, vertices_440, vertices_872, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_13, vertices_69, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_138, vertices_594, vertices_146, vertices_194, vertices_44, vertices_76, vertices_52, vertices_532, vertices_548, vertices_580, vertices_56, vertices_152, vertices_616, vertices_296, vertices_328, vertices_392, vertices_176, vertices_656, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_333), (false, vertices_961), (true, vertices_594), (true, vertices_146), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_152), (true, vertices_616), (true, vertices_296), (true, vertices_176), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_594) then 15 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_616) then 20 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_594), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_616), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 8 594
cert_row_2 1 2 4 5 8 616
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 722
cert_cover_5 2 0 0 3 5 6 594 722 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 44 620 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 56 440 3
cert_coverFacet 6 872
cert_cover_5 6 1 2 4 5 7 616 872 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0310

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0311.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0311

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 333, 961, 598, 666, 706, 428, 372, 696, 880, 928, 7, 11, 67, 131, 13, 69, 265, 193, 321, 385, 22, 70, 26, 138, 530, 194, 578, 642, 44, 268, 52, 84, 292, 324, 56, 664, 168, 392, 368, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_333, vertices_961, vertices_598, vertices_666, vertices_706, vertices_428, vertices_372, vertices_696, vertices_880, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_13, vertices_69, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_138, vertices_530, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_52, vertices_84, vertices_292, vertices_324, vertices_56, vertices_664, vertices_168, vertices_392, vertices_368, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_333), (false, vertices_961), (true, vertices_530), (true, vertices_578), (true, vertices_642), (true, vertices_84), (true, vertices_292), (true, vertices_664), (true, vertices_168), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_664) then 19 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_368) then 21 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_2 1 2 3 6 8 664
cert_row_2 2 3 4 5 7 368
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 0 8 3 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 26 666 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 428
cert_cover_5 3 3 1 2 4 6 44 428 3
cert_coverFacet 4 372
cert_cover_5 4 2 1 3 4 5 52 372 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 880
cert_cover_5 6 2 3 4 5 8 368 880 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0311

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0312.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0312

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 213, 665, 334, 962, 364, 692, 740, 824, 904, 864, 7, 11, 67, 131, 21, 69, 25, 137, 145, 193, 14, 70, 266, 194, 322, 386, 44, 332, 52, 148, 100, 676, 196, 56, 536, 296, 392, 648, 776, 560, 656, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_213, vertices_665, vertices_334, vertices_962, vertices_364, vertices_692, vertices_740, vertices_824, vertices_904, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_25, vertices_137, vertices_145, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_332, vertices_52, vertices_148, vertices_100, vertices_676, vertices_196, vertices_56, vertices_536, vertices_296, vertices_392, vertices_648, vertices_776, vertices_560, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_213), (false, vertices_665), (true, vertices_322), (true, vertices_332), (true, vertices_100), (true, vertices_676), (true, vertices_296), (true, vertices_776), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_665) then 17 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_332) then 18 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_676) then 21 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_2 1 1 4 6 8 676
cert_row_2 2 1 2 5 7 332
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 2 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 364
cert_cover_5 2 2 1 2 4 5 44 364 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 740
cert_cover_5 4 1 1 4 5 6 100 740 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0312

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0313.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0313

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 533, 709, 665, 334, 962, 364, 628, 440, 944, 864, 7, 11, 67, 131, 21, 69, 517, 25, 137, 529, 193, 641, 14, 70, 266, 194, 322, 386, 44, 332, 52, 532, 100, 580, 56, 152, 296, 392, 432, 560, 656, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_533, vertices_709, vertices_665, vertices_334, vertices_962, vertices_364, vertices_628, vertices_440, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_517, vertices_25, vertices_137, vertices_529, vertices_193, vertices_641, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_332, vertices_52, vertices_532, vertices_100, vertices_580, vertices_56, vertices_152, vertices_296, vertices_392, vertices_432, vertices_560, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_533), (false, vertices_709), (false, vertices_665), (true, vertices_322), (true, vertices_332), (true, vertices_100), (true, vertices_296), (true, vertices_432), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_533) then 2 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_332) then 17 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_432) then 21 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 3 4 6 7 432
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 0 6 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 364
cert_cover_5 2 0 1 2 4 5 44 364 3
cert_coverFacet 3 628
cert_cover_5 3 3 1 3 4 5 52 628 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 944
cert_cover_5 5 2 3 4 6 8 432 944 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0313

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0314.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0314

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 533, 709, 665, 334, 962, 364, 628, 440, 880, 912, 7, 11, 67, 131, 21, 69, 517, 25, 137, 529, 193, 641, 14, 70, 266, 194, 322, 386, 44, 332, 52, 532, 100, 580, 56, 152, 296, 392, 624, 304, 400, 656, 784, 352, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_533, vertices_709, vertices_665, vertices_334, vertices_962, vertices_364, vertices_628, vertices_440, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_517, vertices_25, vertices_137, vertices_529, vertices_193, vertices_641, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_332, vertices_52, vertices_532, vertices_100, vertices_580, vertices_56, vertices_152, vertices_296, vertices_392, vertices_624, vertices_304, vertices_400, vertices_656, vertices_784, vertices_352, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_533), (false, vertices_709), (false, vertices_665), (true, vertices_322), (true, vertices_332), (true, vertices_100), (true, vertices_296), (true, vertices_624), (true, vertices_304), (true, vertices_400), (true, vertices_784), (true, vertices_352), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_533) then 2 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_332) then 17 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_624) then 21 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 3 4 5 8 624
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 0 5 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 364
cert_cover_5 2 0 1 2 4 5 44 364 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 440
cert_cover_5 4 3 2 3 4 6 56 440 3
cert_coverFacet 5 880
cert_cover_5 5 2 3 4 5 7 624 880 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0314

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0317.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0317

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 781, 581, 961, 598, 218, 428, 820, 248, 880, 480, 7, 11, 67, 131, 13, 69, 517, 265, 193, 577, 385, 769, 22, 70, 26, 138, 82, 194, 44, 268, 52, 532, 292, 580, 772, 56, 216, 168, 392, 112, 816, 592, 224, 352, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_781, vertices_581, vertices_961, vertices_598, vertices_218, vertices_428, vertices_820, vertices_248, vertices_880, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_13, vertices_69, vertices_517, vertices_265, vertices_193, vertices_577, vertices_385, vertices_769, vertices_22, vertices_70, vertices_26, vertices_138, vertices_82, vertices_194, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_216, vertices_168, vertices_392, vertices_112, vertices_816, vertices_592, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_781), (false, vertices_581), (false, vertices_961), (true, vertices_82), (true, vertices_532), (true, vertices_292), (true, vertices_216), (true, vertices_168), (true, vertices_112), (true, vertices_816), (true, vertices_592), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_581) then 2 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_216) then 18 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_816) then 20 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 19 => Sum.inl 3
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
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_2 1 3 4 7 8 816
cert_row_2 2 2 3 5 6 216
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 0 8 3 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 5 26 218 3
cert_coverFacet 2 428
cert_cover_5 2 3 1 2 4 6 44 428 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 248
cert_cover_5 4 2 2 3 4 5 56 248 3
cert_coverFacet 5 880
cert_cover_5 5 1 3 4 5 7 112 880 3
cert_coverFacet 6 480
cert_cover_2 6 5 4 6 7 224 480 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0317

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0318.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0318

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 579, 597, 425, 817, 398, 198, 962, 220, 248, 624, 992, 7, 11, 67, 515, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 134, 266, 194, 578, 386, 770, 28, 140, 84, 196, 56, 216, 168, 392, 112, 560, 592, 224, 608, 416, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_579, vertices_597, vertices_425, vertices_817, vertices_398, vertices_198, vertices_962, vertices_220, vertices_248, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_134, vertices_266, vertices_194, vertices_578, vertices_386, vertices_770, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_216, vertices_168, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_608, vertices_416, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_579), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_140), (true, vertices_196), (true, vertices_216), (true, vertices_112), (true, vertices_224), (true, vertices_608), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_425) then 16 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_216) then 17 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_960) then 22 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_2 1 5 6 7 8 960
cert_row_4 2 0 1 2 6 7 398 14 3
cert_rows_3
cert_pivot_3 5 3 0
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 28 220 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0318

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0319.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0319

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 597, 217, 270, 838, 962, 428, 820, 632, 744, 928, 7, 11, 67, 131, 21, 69, 25, 137, 81, 193, 14, 70, 262, 266, 194, 834, 386, 44, 268, 52, 532, 292, 580, 772, 56, 88, 616, 168, 200, 392, 560, 592, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_597, vertices_217, vertices_270, vertices_838, vertices_962, vertices_428, vertices_820, vertices_632, vertices_744, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_25, vertices_137, vertices_81, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_194, vertices_834, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_88, vertices_616, vertices_168, vertices_200, vertices_392, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_597), (false, vertices_217), (true, vertices_262), (true, vertices_834), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_616), (true, vertices_168), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_834) then 15 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_616) then 21 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
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
cert_row_2 0 0 5 7 8 834
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
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 428
cert_cover_5 3 2 1 2 4 6 44 428 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 632
cert_cover_5 5 1 2 3 4 5 56 632 3
cert_coverFacet 6 744
cert_cover_5 6 1 2 4 5 6 616 744 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0319

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0322.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0322

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 333, 961, 214, 282, 914, 108, 692, 740, 824, 872, 7, 11, 67, 131, 13, 69, 265, 193, 321, 385, 22, 70, 26, 266, 146, 274, 194, 386, 44, 76, 52, 148, 100, 676, 196, 56, 280, 104, 808, 328, 560, 656, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_333, vertices_961, vertices_214, vertices_282, vertices_914, vertices_108, vertices_692, vertices_740, vertices_824, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_13, vertices_69, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_274, vertices_194, vertices_386, vertices_44, vertices_76, vertices_52, vertices_148, vertices_100, vertices_676, vertices_196, vertices_56, vertices_280, vertices_104, vertices_808, vertices_328, vertices_560, vertices_656, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_333), (false, vertices_961), (true, vertices_146), (true, vertices_274), (true, vertices_148), (true, vertices_100), (true, vertices_676), (true, vertices_196), (true, vertices_280), (true, vertices_104), (true, vertices_808), (true, vertices_560), (true, vertices_656), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_676) then 18 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_808) then 20 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 7 8 808
cert_row_2 1 1 4 6 8 676
cert_row_4 2 0 1 3 5 6 214 22 3
cert_row_4 3 0 3 6 7 8 914 146 3
cert_rows
cert_pivot_2 2 4 1 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 22 214 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 914
cert_cover_5 2 3 0 3 6 7 146 914 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 100 740 3
cert_coverFacet 6 824
cert_cover_5 6 0 2 3 4 7 56 824 3
cert_coverFacet 7 872
cert_cover_5 7 0 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0322

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0323.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0323

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 333, 961, 214, 794, 914, 108, 692, 740, 568, 872, 7, 11, 67, 131, 13, 69, 265, 193, 321, 385, 22, 70, 26, 266, 146, 786, 194, 386, 44, 76, 52, 148, 100, 676, 196, 56, 536, 104, 552, 328, 776, 560, 656, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_333, vertices_961, vertices_214, vertices_794, vertices_914, vertices_108, vertices_692, vertices_740, vertices_568, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_13, vertices_69, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_786, vertices_194, vertices_386, vertices_44, vertices_76, vertices_52, vertices_148, vertices_100, vertices_676, vertices_196, vertices_56, vertices_536, vertices_104, vertices_552, vertices_328, vertices_776, vertices_560, vertices_656, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_333), (false, vertices_961), (true, vertices_146), (true, vertices_786), (true, vertices_148), (true, vertices_100), (true, vertices_676), (true, vertices_196), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_656), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_786) then 15 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_676) then 19 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 5 7 8 872 104 3
cert_row_2 1 0 3 7 8 786
cert_row_2 2 1 4 6 8 676
cert_row_4 3 0 1 3 5 6 214 22 3
cert_rows
cert_pivot_2 2 7 4 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 3 0 1 3 5 22 214 3
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 26 794 3
cert_coverFacet 2 914
cert_cover_5 2 1 0 3 6 7 146 914 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 100 740 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 872
cert_cover_5 7 0 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0323

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0324.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0324

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 213, 793, 913, 334, 962, 812, 116, 868, 568, 752, 7, 11, 67, 131, 21, 69, 25, 265, 145, 785, 193, 385, 14, 70, 266, 194, 322, 386, 44, 268, 52, 84, 100, 804, 324, 56, 536, 552, 776, 112, 560, 208, 656, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_213, vertices_793, vertices_913, vertices_334, vertices_962, vertices_812, vertices_116, vertices_868, vertices_568, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_785, vertices_193, vertices_385, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_52, vertices_84, vertices_100, vertices_804, vertices_324, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_213), (false, vertices_793), (false, vertices_913), (true, vertices_322), (true, vertices_268), (true, vertices_100), (true, vertices_804), (true, vertices_324), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_608), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_804) then 17 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_2 1 1 4 7 8 804
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 194 962 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 868
cert_cover_5 4 1 1 4 5 7 100 868 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0324

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0325.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0325

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 213, 281, 913, 334, 962, 364, 692, 740, 824, 864, 7, 11, 67, 131, 21, 69, 25, 265, 145, 273, 193, 385, 14, 70, 266, 194, 322, 386, 44, 332, 52, 148, 100, 676, 196, 56, 280, 296, 560, 656, 784, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_213, vertices_281, vertices_913, vertices_334, vertices_962, vertices_364, vertices_692, vertices_740, vertices_824, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_273, vertices_193, vertices_385, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_332, vertices_52, vertices_148, vertices_100, vertices_676, vertices_196, vertices_56, vertices_280, vertices_296, vertices_560, vertices_656, vertices_784, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_213), (false, vertices_281), (false, vertices_913), (true, vertices_322), (true, vertices_332), (true, vertices_100), (true, vertices_676), (true, vertices_296), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 17 14 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_281) then 2 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_332) then 16 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_676) then 19 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_2 1 1 4 6 8 676
cert_row_2 2 1 2 5 7 332
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 2 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 364
cert_cover_5 2 2 1 2 4 5 44 364 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 740
cert_cover_5 4 1 1 4 5 6 100 740 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0325

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0326.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0326

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 149, 709, 617, 689, 398, 198, 962, 412, 376, 880, 912, 7, 11, 67, 21, 69, 133, 41, 73, 49, 145, 545, 577, 641, 14, 70, 134, 266, 194, 322, 386, 28, 396, 148, 196, 56, 280, 104, 328, 368, 560, 400, 656, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_149, vertices_709, vertices_617, vertices_689, vertices_398, vertices_198, vertices_962, vertices_412, vertices_376, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_133, vertices_41, vertices_73, vertices_49, vertices_145, vertices_545, vertices_577, vertices_641, vertices_14, vertices_70, vertices_134, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_396, vertices_148, vertices_196, vertices_56, vertices_280, vertices_104, vertices_328, vertices_368, vertices_560, vertices_400, vertices_656, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_149), (false, vertices_709), (false, vertices_617), (false, vertices_689), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_280), (true, vertices_368), (true, vertices_400), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_709) then 14 else
  if p.val = (false, vertices_617) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_368) then 20 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_2 1 3 4 5 7 368
cert_row_4 2 0 5 6 7 8 962 194 3
cert_rows_3
cert_pivot_3 3 1 0
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 194 962 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 28 412 3
cert_coverFacet 4 376
cert_cover_5 4 1 2 3 4 5 56 376 3
cert_coverFacet 5 880
cert_cover_5 5 1 3 4 5 8 368 880 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0326

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0327.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0327

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 661, 709, 105, 625, 398, 198, 962, 412, 312, 872, 944, 7, 11, 67, 21, 69, 645, 41, 73, 49, 529, 97, 577, 14, 70, 134, 266, 194, 322, 386, 28, 396, 148, 196, 56, 280, 104, 296, 328, 304, 560, 400, 656, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_661, vertices_709, vertices_105, vertices_625, vertices_398, vertices_198, vertices_962, vertices_412, vertices_312, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_645, vertices_41, vertices_73, vertices_49, vertices_529, vertices_97, vertices_577, vertices_14, vertices_70, vertices_134, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_396, vertices_148, vertices_196, vertices_56, vertices_280, vertices_104, vertices_296, vertices_328, vertices_304, vertices_560, vertices_400, vertices_656, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_661), (false, vertices_709), (false, vertices_105), (false, vertices_625), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_280), (true, vertices_296), (true, vertices_304), (true, vertices_400), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 17 14 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_105) then 1 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_396) then 16 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 28 412 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0327

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0328.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0328

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 661, 709, 617, 561, 398, 198, 962, 412, 376, 944, 864, 7, 11, 67, 21, 69, 645, 41, 73, 49, 529, 545, 577, 14, 70, 134, 266, 194, 322, 386, 28, 396, 148, 196, 56, 280, 104, 328, 304, 560, 400, 656, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_661, vertices_709, vertices_617, vertices_561, vertices_398, vertices_198, vertices_962, vertices_412, vertices_376, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_645, vertices_41, vertices_73, vertices_49, vertices_529, vertices_545, vertices_577, vertices_14, vertices_70, vertices_134, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_396, vertices_148, vertices_196, vertices_56, vertices_280, vertices_104, vertices_328, vertices_304, vertices_560, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_661), (false, vertices_709), (false, vertices_617), (false, vertices_561), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_280), (true, vertices_304), (true, vertices_400), (true, vertices_352), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 14 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 28 412 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 304 944 2
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0328

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0329.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0329

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 149, 709, 617, 689, 398, 198, 962, 412, 376, 944, 864, 7, 11, 67, 21, 69, 133, 41, 73, 49, 145, 545, 577, 641, 14, 70, 134, 266, 194, 322, 386, 28, 396, 148, 196, 56, 280, 104, 328, 688, 304, 400, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_149, vertices_709, vertices_617, vertices_689, vertices_398, vertices_198, vertices_962, vertices_412, vertices_376, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_133, vertices_41, vertices_73, vertices_49, vertices_145, vertices_545, vertices_577, vertices_641, vertices_14, vertices_70, vertices_134, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_396, vertices_148, vertices_196, vertices_56, vertices_280, vertices_104, vertices_328, vertices_688, vertices_304, vertices_400, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_149), (false, vertices_709), (false, vertices_617), (false, vertices_689), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_280), (true, vertices_304), (true, vertices_400), (true, vertices_352), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_709) then 16 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 3 4 6 8 688
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 0 6 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 28 412 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 944
cert_cover_5 5 2 3 4 6 7 688 944 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0329

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0330.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0330

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 195, 899, 213, 409, 590, 706, 812, 628, 312, 496, 992, 7, 11, 67, 131, 771, 21, 69, 25, 265, 145, 193, 385, 14, 70, 522, 194, 578, 642, 44, 524, 52, 84, 548, 580, 56, 280, 296, 776, 112, 304, 208, 400, 480, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_195, vertices_899, vertices_213, vertices_409, vertices_590, vertices_706, vertices_812, vertices_628, vertices_312, vertices_496, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_771, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_522, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_280, vertices_296, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_480, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_195), (false, vertices_899), (false, vertices_213), (false, vertices_409), (true, vertices_578), (true, vertices_524), (true, vertices_548), (true, vertices_580), (true, vertices_296), (true, vertices_112), (true, vertices_304), (true, vertices_480), (true, vertices_608), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_480) then 22 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 6 7 480
cert_row_4 1 0 1 2 5 8 590 14 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 14 590 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 3 1 3 4 5 52 628 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 496
cert_cover_5 5 0 3 4 5 6 112 496 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 8 480 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0330

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0331.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0331

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 809, 625, 782, 198, 902, 706, 412, 440, 240, 992, 7, 11, 67, 21, 69, 41, 521, 49, 81, 545, 577, 14, 70, 134, 774, 522, 194, 578, 642, 28, 268, 148, 196, 388, 56, 408, 296, 776, 112, 176, 208, 224, 608, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_809, vertices_625, vertices_782, vertices_198, vertices_902, vertices_706, vertices_412, vertices_440, vertices_240, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_70, vertices_134, vertices_774, vertices_522, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_112, vertices_176, vertices_208, vertices_224, vertices_608, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_809), (false, vertices_625), (true, vertices_134), (true, vertices_774), (true, vertices_194), (true, vertices_642), (true, vertices_268), (true, vertices_388), (true, vertices_408), (true, vertices_176), (true, vertices_224), (true, vertices_416), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_774) then 13 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_408) then 19 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_2 1 0 1 7 8 774
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 0 2 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 902
cert_cover_5 2 1 0 1 6 7 134 902 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 412
cert_cover_5 4 0 1 2 3 6 28 412 3
cert_coverFacet 5 440
cert_cover_5 5 0 2 3 4 6 56 440 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coverFacet 7 992
cert_cover_5 7 2 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0331

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0332.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0332

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 617, 369, 782, 198, 902, 706, 412, 824, 464, 992, 7, 11, 67, 21, 69, 41, 585, 49, 81, 97, 14, 70, 134, 774, 522, 194, 578, 642, 28, 268, 148, 196, 388, 56, 280, 552, 776, 304, 208, 336, 400, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_617, vertices_369, vertices_782, vertices_198, vertices_902, vertices_706, vertices_412, vertices_824, vertices_464, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_585, vertices_49, vertices_81, vertices_97, vertices_14, vertices_70, vertices_134, vertices_774, vertices_522, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_617), (false, vertices_369), (true, vertices_134), (true, vertices_774), (true, vertices_194), (true, vertices_642), (true, vertices_268), (true, vertices_388), (true, vertices_280), (true, vertices_776), (true, vertices_400), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 19 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_774) then 14 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 2 3 6 7 412 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 902
cert_cover_5 2 0 0 1 6 7 134 902 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 412
cert_cover_5 4 1 1 2 3 6 28 412 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 352 992 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0332

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0333.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0333

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 617, 433, 225, 782, 198, 902, 706, 412, 824, 992, 7, 11, 67, 21, 69, 41, 585, 49, 145, 97, 161, 193, 14, 70, 134, 774, 522, 194, 578, 642, 28, 268, 148, 196, 388, 56, 280, 552, 776, 304, 400, 224, 608, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_617, vertices_433, vertices_225, vertices_782, vertices_198, vertices_902, vertices_706, vertices_412, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_134, vertices_774, vertices_522, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_617), (false, vertices_433), (false, vertices_225), (true, vertices_134), (true, vertices_774), (true, vertices_194), (true, vertices_642), (true, vertices_268), (true, vertices_388), (true, vertices_280), (true, vertices_776), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_774) then 13 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 2 3 6 7 412 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 902
cert_cover_5 2 0 0 1 6 7 134 902 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 412
cert_cover_5 4 1 1 2 3 6 28 412 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0333

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0357.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0357

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 653, 581, 961, 790, 838, 346, 172, 692, 312, 488, 944, 7, 11, 67, 13, 69, 517, 137, 193, 577, 641, 22, 70, 774, 26, 74, 274, 322, 44, 140, 52, 532, 164, 580, 644, 56, 280, 168, 296, 200, 328, 688, 304, 784, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_653, vertices_581, vertices_961, vertices_790, vertices_838, vertices_346, vertices_172, vertices_692, vertices_312, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_69, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_70, vertices_774, vertices_26, vertices_74, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_580, vertices_644, vertices_56, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_688, vertices_304, vertices_784, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_653), (false, vertices_581), (false, vertices_961), (true, vertices_774), (true, vertices_274), (true, vertices_322), (true, vertices_532), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_688), (true, vertices_304), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_688) then 21 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_2 1 3 4 6 8 688
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 346
cert_cover_5 2 2 0 2 3 5 26 346 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 168 488 2
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 7 688 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0357

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0900 : Certifies 900 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0295.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0901 : Certifies 901 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0296.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0902 : Certifies 902 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0297.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0903 : Certifies 903 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0299.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0904 : Certifies 904 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0300.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0905 : Certifies 905 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0301.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0906 : Certifies 906 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0307.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0907 : Certifies 907 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0308.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0908 : Certifies 908 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0309.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0909 : Certifies 909 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0310.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0910 : Certifies 910 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0311.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0911 : Certifies 911 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0312.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0912 : Certifies 912 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0313.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0913 : Certifies 913 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0314.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0914 : Certifies 914 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0317.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0915 : Certifies 915 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0318.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0916 : Certifies 916 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0319.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0917 : Certifies 917 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0322.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0918 : Certifies 918 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0323.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0919 : Certifies 919 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0324.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0920 : Certifies 920 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0325.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0921 : Certifies 921 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0326.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0922 : Certifies 922 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0327.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0923 : Certifies 923 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0328.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0924 : Certifies 924 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0329.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0925 : Certifies 925 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0330.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0926 : Certifies 926 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0331.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0927 : Certifies 927 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0332.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0928 : Certifies 928 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0333.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0929 : Certifies 929 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0357.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B030 (j : Fin 30) :
    Certifies (900 + j.val) := by
  fin_cases j
  · exact projection_0900
  · exact projection_0901
  · exact projection_0902
  · exact projection_0903
  · exact projection_0904
  · exact projection_0905
  · exact projection_0906
  · exact projection_0907
  · exact projection_0908
  · exact projection_0909
  · exact projection_0910
  · exact projection_0911
  · exact projection_0912
  · exact projection_0913
  · exact projection_0914
  · exact projection_0915
  · exact projection_0916
  · exact projection_0917
  · exact projection_0918
  · exact projection_0919
  · exact projection_0920
  · exact projection_0921
  · exact projection_0922
  · exact projection_0923
  · exact projection_0924
  · exact projection_0925
  · exact projection_0926
  · exact projection_0927
  · exact projection_0928
  · exact projection_0929

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
