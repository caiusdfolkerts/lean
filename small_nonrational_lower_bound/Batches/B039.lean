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
/- Source: ProjectionCertificates/R_one_six_0794.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0794

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 78, 458, 348, 824, 624, 976, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 70, 74, 266, 194, 386, 28, 76, 84, 56, 280, 808, 328, 112, 560, 336, 592, 784, 608, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_78, vertices_458, vertices_348, vertices_824, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_70, vertices_74, vertices_266, vertices_194, vertices_386, vertices_28, vertices_76, vertices_84, vertices_56, vertices_280, vertices_808, vertices_328, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_608, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_74), (true, vertices_76), (true, vertices_280), (true, vertices_328), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_737) then 20 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 7 8 808
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 1 2 3 5 7 348 28 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 4 0 1 3
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 348
cert_cover_5 2 2 1 2 3 5 28 348 3
cert_coverFacet 3 824
cert_cover_5 3 0 2 3 4 7 56 824 3
cert_coverFacet 4 624
cert_cover_2 4 4 3 5 8 112 624 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 336 976 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0794

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0795.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0795

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 899, 117, 553, 737, 78, 458, 348, 824, 496, 928, 7, 11, 131, 771, 53, 69, 41, 521, 97, 545, 193, 641, 14, 70, 74, 266, 194, 386, 28, 76, 84, 56, 280, 552, 328, 776, 112, 304, 336, 224, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_899, vertices_117, vertices_553, vertices_737, vertices_78, vertices_458, vertices_348, vertices_824, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_771, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_545, vertices_193, vertices_641, vertices_14, vertices_70, vertices_74, vertices_266, vertices_194, vertices_386, vertices_28, vertices_76, vertices_84, vertices_56, vertices_280, vertices_552, vertices_328, vertices_776, vertices_112, vertices_304, vertices_336, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_899), (false, vertices_117), (false, vertices_553), (false, vertices_737), (true, vertices_74), (true, vertices_76), (true, vertices_280), (true, vertices_328), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_117) then 12 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_737) then 20 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 3 5 7 348 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 348
cert_cover_5 2 1 1 2 3 5 28 348 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 496
cert_cover_5 4 3 3 4 5 6 112 496 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0795

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0796.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0796

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 899, 117, 553, 737, 78, 458, 348, 824, 624, 976, 7, 11, 131, 771, 53, 69, 41, 521, 97, 545, 193, 641, 14, 70, 74, 266, 194, 386, 28, 76, 84, 56, 280, 552, 328, 776, 112, 560, 336, 592, 784, 608, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_899, vertices_117, vertices_553, vertices_737, vertices_78, vertices_458, vertices_348, vertices_824, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_771, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_545, vertices_193, vertices_641, vertices_14, vertices_70, vertices_74, vertices_266, vertices_194, vertices_386, vertices_28, vertices_76, vertices_84, vertices_56, vertices_280, vertices_552, vertices_328, vertices_776, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_608, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_899), (false, vertices_117), (false, vertices_553), (false, vertices_737), (true, vertices_74), (true, vertices_76), (true, vertices_280), (true, vertices_328), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_117) then 12 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_737) then 20 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 3 5 7 348 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 348
cert_cover_5 2 1 1 2 3 5 28 348 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 624
cert_cover_2 4 4 3 5 8 112 624 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 336 976 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0796

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0797.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0797

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 117, 553, 225, 929, 78, 842, 962, 348, 824, 496, 7, 11, 131, 53, 69, 41, 521, 97, 161, 545, 193, 641, 14, 70, 74, 522, 194, 834, 642, 28, 76, 84, 56, 280, 552, 328, 776, 112, 304, 336, 224, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_117, vertices_553, vertices_225, vertices_929, vertices_78, vertices_842, vertices_962, vertices_348, vertices_824, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_641, vertices_14, vertices_70, vertices_74, vertices_522, vertices_194, vertices_834, vertices_642, vertices_28, vertices_76, vertices_84, vertices_56, vertices_280, vertices_552, vertices_328, vertices_776, vertices_112, vertices_304, vertices_336, vertices_224, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_117), (false, vertices_553), (false, vertices_225), (false, vertices_929), (true, vertices_74), (true, vertices_834), (true, vertices_76), (true, vertices_280), (true, vertices_328), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_117) then 12 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_834) then 16 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 17 => Sum.inl 2
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
cert_row_2 0 0 5 7 8 834
cert_row_4 1 1 2 3 5 7 348 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 348
cert_cover_5 3 1 1 2 3 5 28 348 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0797

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0798.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0798

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 323, 397, 961, 790, 122, 850, 812, 628, 744, 904, 7, 11, 67, 259, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 786, 322, 44, 268, 52, 532, 548, 772, 104, 552, 200, 392, 648, 776, 112, 592, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_323, vertices_397, vertices_961, vertices_790, vertices_122, vertices_850, vertices_812, vertices_628, vertices_744, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_786, vertices_322, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_592, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_323), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_112), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_786) then 15 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_608) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 2 4 5 6 8 744 104 3
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_2 3 0 3 7 8 786
cert_row_2 4 0 2 3 4 58
cert_rows_2
cert_pivot 6 5 1 7 0
cert_heightProof 5
cert_coverFacet 0 790
cert_cover_5 0 3 0 1 3 7 22 790 3
cert_coverFacet 1 122
cert_cover_5 1 4 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 3 0 3 5 7 82 850 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 52 628 3
cert_coverFacet 5 744
cert_cover_5 5 0 2 4 5 6 104 744 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0798

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0799.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0799

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 169, 737, 270, 326, 962, 348, 696, 920, 880, 7, 11, 131, 53, 69, 41, 137, 97, 161, 193, 14, 70, 262, 266, 194, 322, 386, 28, 268, 84, 324, 56, 664, 280, 168, 392, 112, 560, 336, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_169, vertices_737, vertices_270, vertices_326, vertices_962, vertices_348, vertices_696, vertices_920, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_268, vertices_84, vertices_324, vertices_56, vertices_664, vertices_280, vertices_168, vertices_392, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_169), (false, vertices_737), (true, vertices_262), (true, vertices_322), (true, vertices_268), (true, vertices_324), (true, vertices_664), (true, vertices_280), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_664) then 18 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 2 3 5 7 348 28 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 348
cert_cover_5 3 2 1 2 3 5 28 348 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 920
cert_cover_5 5 1 2 3 6 7 664 920 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0799

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0800.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0800

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 681, 737, 270, 326, 962, 348, 568, 920, 880, 7, 11, 131, 53, 69, 41, 137, 97, 673, 193, 14, 70, 262, 266, 194, 322, 386, 28, 268, 84, 324, 56, 280, 536, 552, 392, 648, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_681, vertices_737, vertices_270, vertices_326, vertices_962, vertices_348, vertices_568, vertices_920, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_673, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_268, vertices_84, vertices_324, vertices_56, vertices_280, vertices_536, vertices_552, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_681), (false, vertices_737), (true, vertices_262), (true, vertices_322), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 19 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 2 3 5 7 348 28 3
cert_row_4 2 2 3 6 7 8 920 280 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 348
cert_cover_5 3 1 1 2 3 5 28 348 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 920
cert_cover_5 5 2 2 3 6 7 280 920 2
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0800

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0801.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0801

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 233, 270, 326, 962, 284, 852, 824, 936, 752, 7, 11, 131, 53, 69, 41, 137, 97, 193, 14, 70, 262, 266, 194, 322, 386, 28, 268, 84, 276, 324, 56, 280, 168, 808, 392, 112, 560, 592, 784, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_233, vertices_270, vertices_326, vertices_962, vertices_284, vertices_852, vertices_824, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_268, vertices_84, vertices_276, vertices_324, vertices_56, vertices_280, vertices_168, vertices_808, vertices_392, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_233), (true, vertices_262), (true, vertices_322), (true, vertices_268), (true, vertices_276), (true, vertices_324), (true, vertices_280), (true, vertices_808), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_808) then 21 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 7 8 808
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 824
cert_cover_5 5 0 2 3 4 7 56 824 3
cert_coverFacet 6 936
cert_cover_5 6 0 2 4 6 7 168 936 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0801

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0802.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0802

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 681, 737, 270, 326, 962, 284, 852, 632, 920, 7, 11, 131, 53, 69, 41, 137, 97, 673, 193, 14, 70, 262, 266, 194, 322, 386, 28, 268, 84, 276, 324, 56, 280, 536, 552, 392, 648, 112, 592, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_681, vertices_737, vertices_270, vertices_326, vertices_962, vertices_284, vertices_852, vertices_632, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_673, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_268, vertices_84, vertices_276, vertices_324, vertices_56, vertices_280, vertices_536, vertices_552, vertices_392, vertices_648, vertices_112, vertices_592, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_681), (false, vertices_737), (true, vertices_262), (true, vertices_322), (true, vertices_268), (true, vertices_276), (true, vertices_324), (true, vertices_280), (true, vertices_536), (true, vertices_592), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 19 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 2 3 6 7 8 920 280 2
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 84 852 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 920
cert_cover_5 6 3 2 3 6 7 280 920 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0802

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0803.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0803

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 169, 737, 270, 326, 962, 796, 852, 632, 936, 7, 11, 131, 53, 69, 41, 137, 97, 161, 193, 14, 70, 262, 266, 194, 322, 386, 28, 268, 84, 788, 324, 56, 536, 168, 552, 392, 776, 112, 592, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_169, vertices_737, vertices_270, vertices_326, vertices_962, vertices_796, vertices_852, vertices_632, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_268, vertices_84, vertices_788, vertices_324, vertices_56, vertices_536, vertices_168, vertices_552, vertices_392, vertices_776, vertices_112, vertices_592, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_169), (false, vertices_737), (true, vertices_262), (true, vertices_322), (true, vertices_268), (true, vertices_788), (true, vertices_324), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_592), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 19 14 21 15 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_737) then 18 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_788) then 20 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 4
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 7 8 788
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 796
cert_cover_5 3 0 1 2 3 7 28 796 3
cert_coverFacet 4 852
cert_cover_5 4 0 1 3 5 7 84 852 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 168 936 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0803

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0804.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0804

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 233, 270, 326, 962, 796, 852, 568, 936, 752, 7, 11, 131, 53, 69, 41, 137, 97, 193, 14, 70, 262, 266, 194, 322, 386, 28, 268, 84, 788, 324, 56, 536, 168, 552, 392, 776, 112, 560, 592, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_233, vertices_270, vertices_326, vertices_962, vertices_796, vertices_852, vertices_568, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_268, vertices_84, vertices_788, vertices_324, vertices_56, vertices_536, vertices_168, vertices_552, vertices_392, vertices_776, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_233), (true, vertices_262), (true, vertices_322), (true, vertices_268), (true, vertices_788), (true, vertices_324), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 21 16 23 18 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_233) then 17 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_788) then 22 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 7 8 788
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 4 6 7 8 936 168 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 796
cert_cover_5 3 0 1 2 3 7 28 796 3
cert_coverFacet 4 852
cert_cover_5 4 0 1 3 5 7 84 852 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 936
cert_cover_5 6 2 2 4 6 7 168 936 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0804

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0807.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0807

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 323, 653, 961, 342, 122, 812, 308, 232, 936, 496, 7, 11, 67, 259, 13, 517, 137, 193, 321, 641, 769, 22, 262, 58, 74, 82, 322, 44, 524, 52, 276, 292, 772, 104, 168, 808, 200, 648, 112, 304, 336, 224, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_653, vertices_961, vertices_342, vertices_122, vertices_812, vertices_308, vertices_232, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_517, vertices_137, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_322, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_104, vertices_168, vertices_808, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_224, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_276), (true, vertices_292), (true, vertices_104), (true, vertices_168), (true, vertices_808), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_808) then 18 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 323 82 276 292 104 168 112 304 336 224 416 775 203 653 808
cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 7 8 808
cert_row_2 1 0 2 3 4 58
cert_row_4 2 0 1 3 5 7 342 22 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 2 0 3
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 2 0 1 3 5 22 342 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 936
cert_cover_5 5 0 2 4 6 7 168 936 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0807

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0808.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0808

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 323, 653, 961, 342, 122, 556, 820, 488, 936, 368, 7, 11, 67, 259, 13, 517, 137, 193, 321, 641, 769, 22, 262, 58, 74, 82, 322, 44, 524, 52, 276, 548, 772, 104, 424, 552, 200, 648, 112, 304, 336, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_653, vertices_961, vertices_342, vertices_122, vertices_556, vertices_820, vertices_488, vertices_936, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_517, vertices_137, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_322, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_424, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_276), (true, vertices_548), (true, vertices_104), (true, vertices_424), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_424) then 18 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 323 82 276 548 104 552 112 304 336 352 800 775 203 653 424
cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 7 424
cert_row_2 1 0 2 3 4 58
cert_row_4 2 0 1 3 5 7 342 22 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 2 0 1 3 5 22 342 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 488
cert_cover_5 4 0 2 4 5 6 104 488 3
cert_coverFacet 5 936
cert_cover_5 5 0 2 4 6 8 424 936 3
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0808

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0809.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0809

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 323, 341, 121, 654, 962, 684, 820, 232, 496, 928, 7, 11, 67, 259, 21, 261, 57, 73, 81, 321, 14, 518, 138, 194, 322, 642, 770, 44, 652, 52, 276, 548, 772, 104, 168, 200, 112, 304, 336, 224, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_341, vertices_121, vertices_654, vertices_962, vertices_684, vertices_820, vertices_232, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_304, vertices_336, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_341), (false, vertices_121), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_304), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_652) then 16 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0809

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0810.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0810

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 323, 341, 121, 654, 962, 684, 820, 488, 368, 928, 7, 11, 67, 259, 21, 261, 57, 73, 81, 321, 14, 518, 138, 194, 322, 642, 770, 44, 652, 52, 276, 548, 772, 104, 168, 200, 112, 304, 336, 352, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_341, vertices_121, vertices_654, vertices_962, vertices_684, vertices_820, vertices_488, vertices_368, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_304, vertices_336, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_341), (false, vertices_121), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_304), (true, vertices_352), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_652) then 16 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_2 2 1 2 6 8 652
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 488
cert_cover_5 4 3 2 4 5 6 104 488 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0810

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0811.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0811

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 323, 341, 121, 654, 962, 684, 820, 232, 752, 848, 7, 11, 67, 259, 21, 261, 57, 73, 81, 321, 14, 518, 138, 194, 322, 642, 770, 44, 652, 52, 276, 548, 772, 104, 168, 200, 112, 560, 336, 592, 784, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_341, vertices_121, vertices_654, vertices_962, vertices_684, vertices_820, vertices_232, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_341), (false, vertices_121), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_652) then 16 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0811

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0812.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0812

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 651, 789, 233, 689, 206, 326, 962, 124, 340, 496, 912, 7, 11, 515, 21, 773, 41, 137, 49, 529, 161, 641, 14, 70, 262, 138, 194, 322, 642, 770, 60, 76, 84, 276, 324, 104, 200, 112, 176, 336, 400, 656, 784, 224, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_651, vertices_789, vertices_233, vertices_689, vertices_206, vertices_326, vertices_962, vertices_124, vertices_340, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_773, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_641, vertices_14, vertices_70, vertices_262, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_276, vertices_324, vertices_104, vertices_200, vertices_112, vertices_176, vertices_336, vertices_400, vertices_656, vertices_784, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_651), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_70), (true, vertices_194), (true, vertices_322), (true, vertices_76), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_400), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0812

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0813.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0813

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 117, 233, 782, 326, 962, 796, 340, 696, 880, 736, 7, 11, 131, 53, 69, 41, 137, 97, 193, 14, 70, 262, 522, 194, 322, 642, 770, 28, 780, 84, 276, 324, 56, 536, 168, 648, 112, 560, 336, 784, 224, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_117, vertices_233, vertices_782, vertices_326, vertices_962, vertices_796, vertices_340, vertices_696, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_780, vertices_84, vertices_276, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_117), (false, vertices_233), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_780), (true, vertices_276), (true, vertices_324), (true, vertices_536), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_608), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_780) then 19 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 796
cert_cover_5 3 0 1 2 3 7 28 796 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0813

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0830.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0830

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 86, 122, 300, 820, 852, 232, 936, 752, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 70, 58, 74, 82, 44, 268, 52, 84, 788, 292, 324, 104, 168, 296, 200, 392, 112, 560, 592, 224, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_86, vertices_122, vertices_300, vertices_820, vertices_852, vertices_232, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_58, vertices_74, vertices_82, vertices_44, vertices_268, vertices_52, vertices_84, vertices_788, vertices_292, vertices_324, vertices_104, vertices_168, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_788), (true, vertices_292), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_788) then 18 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 82 1 84 292 104 168 296 112 560 592 224 672 800 327 203 397 788
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_2 1 1 3 7 8 788
cert_row_4 2 2 4 6 7 8 936 168 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 84 852 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 936
cert_cover_5 6 2 2 4 6 7 168 936 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0830

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0831.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0831

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 86, 122, 812, 564, 852, 232, 936, 752, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 70, 58, 74, 82, 44, 268, 52, 84, 532, 548, 324, 772, 104, 168, 808, 200, 392, 112, 560, 592, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_86, vertices_122, vertices_812, vertices_564, vertices_852, vertices_232, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_58, vertices_74, vertices_82, vertices_44, vertices_268, vertices_52, vertices_84, vertices_532, vertices_548, vertices_324, vertices_772, vertices_104, vertices_168, vertices_808, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_104), (true, vertices_168), (true, vertices_808), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_808) then 19 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_26 82 84 532 548 772 104 168 112 560 592 224 672 327 203 397 808
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_2 1 2 4 7 8 808
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 936
cert_cover_5 6 1 2 4 6 7 168 936 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0831

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0834.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0834

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 86, 122, 172, 436, 852, 744, 624, 944, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 70, 58, 74, 82, 44, 140, 52, 84, 276, 164, 324, 388, 104, 168, 200, 112, 432, 560, 592, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_86, vertices_122, vertices_172, vertices_436, vertices_852, vertices_744, vertices_624, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_58, vertices_74, vertices_82, vertices_44, vertices_140, vertices_52, vertices_84, vertices_276, vertices_164, vertices_324, vertices_388, vertices_104, vertices_168, vertices_200, vertices_112, vertices_432, vertices_560, vertices_592, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_276), (true, vertices_164), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_432) then 20 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_2 2 3 4 6 7 432
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 52 436 3
cert_coverFacet 4 852
cert_cover_5 4 1 1 3 5 7 84 852 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coverFacet 7 944
cert_cover_5 7 2 3 4 6 8 432 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0834

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0835.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0835

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 86, 122, 172, 692, 340, 916, 744, 880, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 70, 58, 74, 82, 44, 140, 52, 84, 660, 276, 164, 324, 388, 104, 168, 200, 112, 560, 336, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_86, vertices_122, vertices_172, vertices_692, vertices_340, vertices_916, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_58, vertices_74, vertices_82, vertices_44, vertices_140, vertices_52, vertices_84, vertices_660, vertices_276, vertices_164, vertices_324, vertices_388, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_660), (true, vertices_276), (true, vertices_164), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_660) then 18 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 82 1 84 276 164 104 168 112 560 336 784 608 672 327 203 397 660
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_2 1 1 3 6 8 660
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 916
cert_cover_5 5 1 1 3 6 7 660 916 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 104 744 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0835

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0836.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0836

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 86, 122, 684, 564, 340, 916, 744, 880, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 70, 58, 74, 82, 44, 140, 52, 84, 276, 532, 548, 324, 388, 644, 104, 680, 200, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_86, vertices_122, vertices_684, vertices_564, vertices_340, vertices_916, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_58, vertices_74, vertices_82, vertices_44, vertices_140, vertices_52, vertices_84, vertices_276, vertices_532, vertices_548, vertices_324, vertices_388, vertices_644, vertices_104, vertices_680, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_104), (true, vertices_680), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_680) then 19 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
cert_nodeAtPriority_26 82 84 276 532 548 644 104 112 560 336 784 608 327 203 397 680
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_2 1 2 4 6 8 680
cert_row_4 2 1 3 6 7 8 916 276 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 916
cert_cover_5 5 2 1 3 6 7 276 916 2
cert_coverFacet 6 744
cert_cover_5 6 1 2 4 5 6 104 744 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0836

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0837.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0837

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 425, 737, 334, 962, 92, 312, 856, 624, 944, 7, 11, 131, 53, 69, 41, 393, 97, 161, 193, 14, 70, 266, 194, 322, 386, 28, 76, 84, 56, 88, 280, 296, 328, 112, 304, 560, 592, 784, 608, 416, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_425, vertices_737, vertices_334, vertices_962, vertices_92, vertices_312, vertices_856, vertices_624, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_393, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_76, vertices_84, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_112, vertices_304, vertices_560, vertices_592, vertices_784, vertices_608, vertices_416, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_425), (false, vertices_737), (true, vertices_322), (true, vertices_76), (true, vertices_88), (true, vertices_280), (true, vertices_328), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_322) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_88) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 312
cert_cover_2 3 3 2 4 7 56 312 3
cert_coverFacet 4 856
cert_cover_5 4 2 2 3 5 7 88 856 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0837

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0843.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0843

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 598, 122, 812, 564, 836, 232, 936, 752, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 70, 58, 74, 82, 44, 268, 52, 532, 548, 324, 580, 772, 104, 168, 808, 200, 392, 112, 560, 592, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_598, vertices_122, vertices_812, vertices_564, vertices_836, vertices_232, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_58, vertices_74, vertices_82, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_808, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_772), (true, vertices_104), (true, vertices_168), (true, vertices_808), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_808) then 19 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_26 82 532 548 580 772 104 168 112 560 592 224 672 327 203 397 808
cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 7 8 808
cert_row_2 1 0 2 3 4 58
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 2 0 3
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 22 598 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 936
cert_cover_5 6 0 2 4 6 7 168 936 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0843

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0844.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0844

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 598, 122, 300, 820, 836, 744, 936, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 70, 58, 74, 82, 44, 268, 52, 532, 292, 324, 580, 772, 104, 680, 296, 200, 392, 112, 560, 592, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_598, vertices_122, vertices_300, vertices_820, vertices_836, vertices_744, vertices_936, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_58, vertices_74, vertices_82, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_324, vertices_580, vertices_772, vertices_104, vertices_680, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_532), (true, vertices_292), (true, vertices_580), (true, vertices_772), (true, vertices_104), (true, vertices_680), (true, vertices_296), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_680) then 19 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_26 82 532 292 580 772 104 296 112 560 592 608 800 327 203 397 680
cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 8 680
cert_row_2 1 0 2 3 4 58
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 22 598 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 744
cert_cover_5 5 0 2 4 5 6 104 744 3
cert_coverFacet 6 936
cert_cover_5 6 0 2 4 6 7 680 936 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0844

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0847.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0847

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 597, 121, 398, 962, 428, 820, 836, 232, 752, 928, 7, 11, 67, 21, 69, 57, 73, 81, 14, 262, 138, 194, 322, 386, 44, 396, 52, 532, 292, 324, 580, 772, 104, 168, 200, 112, 560, 592, 224, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_597, vertices_121, vertices_398, vertices_962, vertices_428, vertices_820, vertices_836, vertices_232, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_57, vertices_73, vertices_81, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_532, vertices_292, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_224, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_597), (false, vertices_121), (true, vertices_386), (true, vertices_396), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_560), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 428
cert_cover_5 2 0 1 2 4 6 44 428 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0847

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0848.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0848

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 597, 121, 398, 962, 428, 820, 836, 744, 624, 928, 7, 11, 67, 21, 69, 57, 73, 81, 14, 262, 138, 194, 322, 386, 44, 396, 52, 532, 292, 324, 580, 772, 104, 168, 200, 112, 560, 592, 608, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_597, vertices_121, vertices_398, vertices_962, vertices_428, vertices_820, vertices_836, vertices_744, vertices_624, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_57, vertices_73, vertices_81, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_532, vertices_292, vertices_324, vertices_580, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_608, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_597), (false, vertices_121), (true, vertices_386), (true, vertices_396), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_560), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (true, vertices_386) then 0 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_2 2 1 2 6 7 396
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0848

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0863.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0863

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 278, 122, 850, 812, 820, 744, 904, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 268, 52, 276, 804, 104, 552, 200, 392, 648, 776, 112, 560, 592, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_850, vertices_812, vertices_820, vertices_744, vertices_904, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_268, vertices_52, vertices_276, vertices_804, vertices_104, vertices_552, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_276), (true, vertices_804), (true, vertices_104), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_804) then 18 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 82 1 274 276 104 552 648 776 112 560 592 784 608 327 203 397 804
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 82 850 3
cert_coverFacet 3 812
cert_cover_5 3 0 1 2 4 7 44 812 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0863

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0864.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0864

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 278, 122, 850, 300, 820, 744, 936, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 268, 52, 276, 292, 104, 680, 296, 200, 392, 112, 560, 592, 784, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_850, vertices_300, vertices_820, vertices_744, vertices_936, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_104, vertices_680, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_784, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_276), (true, vertices_292), (true, vertices_104), (true, vertices_680), (true, vertices_296), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_680) then 19 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_26 82 274 276 292 104 296 112 560 592 784 608 800 327 203 397 680
cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 8 680
cert_row_2 1 0 2 3 4 58
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 744
cert_cover_5 5 0 2 4 5 6 104 744 3
cert_coverFacet 6 936
cert_cover_5 6 0 2 4 6 7 680 936 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0864

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1170 : Certifies 1170 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0794.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1171 : Certifies 1171 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0795.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1172 : Certifies 1172 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0796.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1173 : Certifies 1173 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0797.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1174 : Certifies 1174 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0798.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1175 : Certifies 1175 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0799.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1176 : Certifies 1176 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0800.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1177 : Certifies 1177 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0801.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1178 : Certifies 1178 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0802.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1179 : Certifies 1179 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0803.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1180 : Certifies 1180 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0804.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1181 : Certifies 1181 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0807.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1182 : Certifies 1182 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0808.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1183 : Certifies 1183 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0809.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1184 : Certifies 1184 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0810.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1185 : Certifies 1185 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0811.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1186 : Certifies 1186 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0812.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1187 : Certifies 1187 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0813.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1188 : Certifies 1188 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0830.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1189 : Certifies 1189 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0831.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1190 : Certifies 1190 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0834.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1191 : Certifies 1191 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0835.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1192 : Certifies 1192 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0836.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1193 : Certifies 1193 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0837.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1194 : Certifies 1194 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0843.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1195 : Certifies 1195 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0844.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1196 : Certifies 1196 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0847.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1197 : Certifies 1197 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0848.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1198 : Certifies 1198 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0863.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1199 : Certifies 1199 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0864.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B039 (j : Fin 30) :
    Certifies (1170 + j.val) := by
  fin_cases j
  · exact projection_1170
  · exact projection_1171
  · exact projection_1172
  · exact projection_1173
  · exact projection_1174
  · exact projection_1175
  · exact projection_1176
  · exact projection_1177
  · exact projection_1178
  · exact projection_1179
  · exact projection_1180
  · exact projection_1181
  · exact projection_1182
  · exact projection_1183
  · exact projection_1184
  · exact projection_1185
  · exact projection_1186
  · exact projection_1187
  · exact projection_1188
  · exact projection_1189
  · exact projection_1190
  · exact projection_1191
  · exact projection_1192
  · exact projection_1193
  · exact projection_1194
  · exact projection_1195
  · exact projection_1196
  · exact projection_1197
  · exact projection_1198
  · exact projection_1199

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
