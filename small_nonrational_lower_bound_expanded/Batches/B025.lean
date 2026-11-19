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
/- Source: ProjectionCertificates/R_one_six_0102.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0102

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 809, 689, 206, 458, 156, 724, 440, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 545, 577, 769, 14, 70, 202, 266, 322, 28, 140, 596, 148, 196, 56, 152, 296, 392, 176, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_809, vertices_689, vertices_206, vertices_458, vertices_156, vertices_724, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_577, vertices_769, vertices_14, vertices_70, vertices_202, vertices_266, vertices_322, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_176, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_809), (false, vertices_689), (true, vertices_202), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (true, vertices_202) then 12 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
cert_nodeAtPriority_3 267 140 148 196 152 392 416 448 704 835 202 597 809 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 596 724 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0102

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0103.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0103

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 425, 817, 206, 458, 156, 724, 696, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 202, 266, 322, 28, 140, 596, 148, 196, 56, 152, 168, 392, 560, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_425, vertices_817, vertices_206, vertices_458, vertices_156, vertices_724, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_202, vertices_266, vertices_322, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_168, vertices_392, vertices_560, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_202), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (true, vertices_202) then 12 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
cert_nodeAtPriority_3 267 140 148 196 152 656 672 448 704 835 202 597 425 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 596 724 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0103

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0106.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0106

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 213, 617, 241, 270, 454, 796, 916, 696, 840, 992, 7, 11, 67, 21, 69, 41, 73, 49, 209, 97, 14, 70, 262, 266, 322, 28, 268, 148, 788, 196, 388, 56, 536, 552, 328, 584, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_213, vertices_617, vertices_241, vertices_270, vertices_454, vertices_796, vertices_916, vertices_696, vertices_840, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_73, vertices_49, vertices_209, vertices_97, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_148, vertices_788, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_788), (true, vertices_388), (true, vertices_536), (true, vertices_776), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 16 13 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_617) then 15 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_788) then 17 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 3 7 8 788
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 148 916 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0106

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0107.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0107

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 597, 617, 689, 270, 454, 412, 724, 440, 360, 992, 7, 11, 67, 21, 69, 41, 73, 49, 529, 545, 577, 14, 70, 262, 266, 322, 28, 268, 596, 148, 196, 388, 56, 408, 104, 296, 328, 176, 656, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_597, vertices_617, vertices_689, vertices_270, vertices_454, vertices_412, vertices_724, vertices_440, vertices_360, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_73, vertices_49, vertices_529, vertices_545, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_596, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_104, vertices_296, vertices_328, vertices_176, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_597), (false, vertices_617), (false, vertices_689), (true, vertices_262), (true, vertices_268), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_408), (true, vertices_296), (true, vertices_352), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_617) then 17 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_408) then 18 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
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
cert_row_2 0 2 3 6 7 408
cert_row_2 1 1 3 5 8 596
cert_row_4 2 0 1 5 6 7 454 70 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 2 3 0 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 28 412 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 596 724 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 360
cert_cover_2 5 4 2 5 7 104 360 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0107

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0108.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0108

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 451, 661, 709, 409, 334, 620, 564, 376, 944, 992, 7, 11, 67, 259, 21, 69, 645, 25, 265, 145, 193, 385, 14, 70, 266, 322, 44, 76, 52, 532, 548, 580, 56, 280, 104, 328, 304, 560, 400, 656, 352, 608, 928, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_451, vertices_661, vertices_709, vertices_409, vertices_334, vertices_620, vertices_564, vertices_376, vertices_944, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_645, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_76, vertices_52, vertices_532, vertices_548, vertices_580, vertices_56, vertices_280, vertices_104, vertices_328, vertices_304, vertices_560, vertices_400, vertices_656, vertices_352, vertices_608, vertices_928, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_451), (false, vertices_661), (false, vertices_709), (false, vertices_409), (true, vertices_76), (true, vertices_548), (true, vertices_104), (true, vertices_328), (true, vertices_304), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_928)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_451) then 11 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_709) then 15 else
  if p.val = (false, vertices_409) then 17 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_928) then 20 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(true, vertices_928), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 6 7 8 928
cert_row_4 1 0 1 2 5 7 334 14 3
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 14 334 3
cert_coverFacet 1 620
cert_cover_5 1 2 1 2 4 5 44 620 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 376
cert_cover_5 3 3 2 3 4 5 56 376 3
cert_coverFacet 4 944
cert_cover_5 4 0 3 4 6 7 304 944 2
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0108

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0109.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0109

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 213, 361, 625, 270, 454, 668, 908, 824, 720, 992, 7, 11, 67, 21, 69, 41, 329, 49, 81, 97, 14, 70, 262, 266, 322, 28, 652, 268, 148, 196, 388, 56, 536, 296, 776, 560, 208, 592, 656, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_213, vertices_361, vertices_625, vertices_270, vertices_454, vertices_668, vertices_908, vertices_824, vertices_720, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_329, vertices_49, vertices_81, vertices_97, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_652, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_213), (false, vertices_361), (false, vertices_625), (true, vertices_262), (true, vertices_652), (true, vertices_268), (true, vertices_388), (true, vertices_536), (true, vertices_776), (true, vertices_656), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 12 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_213) then 14 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_652) then 15 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 2 6 8 652
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 652 908 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 720
cert_cover_2 5 5 3 6 8 208 720 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0109

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0110.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0110

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 213, 361, 689, 225, 270, 454, 668, 908, 824, 992, 7, 11, 67, 21, 69, 41, 329, 49, 145, 97, 161, 193, 14, 70, 262, 266, 322, 28, 652, 268, 148, 196, 388, 56, 536, 296, 776, 560, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_213, vertices_361, vertices_689, vertices_225, vertices_270, vertices_454, vertices_668, vertices_908, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_329, vertices_49, vertices_145, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_652, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_213), (false, vertices_361), (false, vertices_689), (false, vertices_225), (true, vertices_262), (true, vertices_652), (true, vertices_268), (true, vertices_388), (true, vertices_536), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 11 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_213) then 13 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_652) then 14 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 2 6 8 652
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 652 908 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0110

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0111.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0111

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 809, 689, 270, 454, 412, 724, 440, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 545, 577, 769, 14, 70, 262, 266, 322, 28, 268, 596, 148, 196, 388, 56, 408, 296, 176, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_809, vertices_689, vertices_270, vertices_454, vertices_412, vertices_724, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_577, vertices_769, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_596, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_296, vertices_176, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_809), (false, vertices_689), (true, vertices_262), (true, vertices_268), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_408), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_408) then 17 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_2 1 1 3 5 8 596
cert_row_4 2 0 1 5 6 7 454 70 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 2 3 0 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 28 412 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 596 724 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0111

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0112.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0112

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 835, 85, 681, 625, 270, 454, 220, 908, 248, 992, 7, 11, 67, 771, 21, 69, 41, 521, 49, 81, 545, 577, 14, 70, 262, 266, 322, 28, 140, 268, 84, 196, 388, 56, 216, 168, 648, 776, 112, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_835, vertices_85, vertices_681, vertices_625, vertices_270, vertices_454, vertices_220, vertices_908, vertices_248, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_140, vertices_268, vertices_84, vertices_196, vertices_388, vertices_56, vertices_216, vertices_168, vertices_648, vertices_776, vertices_112, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_835), (false, vertices_85), (false, vertices_681), (false, vertices_625), (true, vertices_262), (true, vertices_140), (true, vertices_268), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_224), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_681) then 16 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_216) then 17 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 1 2 6 7 8 908 140 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 3 0 1 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 28 220 3
cert_coverFacet 3 908
cert_cover_5 3 2 1 2 6 7 140 908 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0112

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0113.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0113

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 451, 213, 409, 782, 838, 556, 628, 248, 936, 992, 7, 11, 67, 259, 21, 69, 25, 265, 145, 193, 385, 14, 70, 774, 266, 322, 44, 524, 52, 84, 548, 580, 56, 152, 168, 552, 392, 776, 112, 208, 224, 608, 928, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_451, vertices_213, vertices_409, vertices_782, vertices_838, vertices_556, vertices_628, vertices_248, vertices_936, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_774, vertices_266, vertices_322, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_152, vertices_168, vertices_552, vertices_392, vertices_776, vertices_112, vertices_208, vertices_224, vertices_608, vertices_928, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_451), (false, vertices_213), (false, vertices_409), (true, vertices_774), (true, vertices_524), (true, vertices_548), (true, vertices_580), (true, vertices_168), (true, vertices_552), (true, vertices_776), (true, vertices_112), (true, vertices_224), (true, vertices_608), (true, vertices_928), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (true, vertices_774) then 14 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_928) then 22 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(true, vertices_928), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_2 1 4 6 7 8 928
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 248
cert_cover_5 4 3 2 3 4 5 56 248 3
cert_coverFacet 5 936
cert_cover_5 5 1 2 4 6 7 168 936 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0113

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0114.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0114

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 835, 213, 617, 241, 270, 454, 412, 696, 904, 992, 7, 11, 67, 771, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 266, 322, 28, 268, 148, 196, 388, 56, 152, 552, 392, 648, 776, 176, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_835, vertices_213, vertices_617, vertices_241, vertices_270, vertices_454, vertices_412, vertices_696, vertices_904, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_152, vertices_552, vertices_392, vertices_648, vertices_776, vertices_176, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 2 3 6 7 412 28 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 412
cert_cover_5 2 1 1 2 3 6 28 412 3
cert_coverFacet 3 696
cert_cover_5 3 2 2 3 4 6 56 696 3
cert_coverFacet 4 904
cert_cover_2 4 6 2 7 8 392 904 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0114

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0115.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0115

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 835, 213, 617, 241, 270, 454, 156, 908, 696, 992, 7, 11, 67, 771, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 266, 322, 28, 140, 268, 148, 196, 388, 56, 152, 552, 648, 776, 176, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_835, vertices_213, vertices_617, vertices_241, vertices_270, vertices_454, vertices_156, vertices_908, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_140, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_152, vertices_552, vertices_648, vertices_776, vertices_176, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_140), (true, vertices_268), (true, vertices_388), (true, vertices_152), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 2 6 7 8 908 140 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 140 908 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0115

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0116.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0116

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 835, 213, 617, 241, 270, 454, 412, 824, 432, 992, 7, 11, 67, 771, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 266, 322, 28, 268, 148, 196, 388, 56, 280, 552, 776, 176, 304, 400, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_835, vertices_213, vertices_617, vertices_241, vertices_270, vertices_454, vertices_412, vertices_824, vertices_432, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_176, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_388), (true, vertices_280), (true, vertices_304), (true, vertices_400), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 2 3 6 7 412 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 412
cert_cover_5 2 1 1 2 3 6 28 412 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 432
cert_cover_2 4 4 3 6 7 176 432 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0116

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0117.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0117

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 333, 214, 666, 898, 620, 244, 696, 840, 992, 7, 11, 67, 259, 13, 69, 265, 321, 22, 70, 26, 522, 146, 194, 386, 642, 770, 44, 76, 52, 212, 100, 56, 664, 552, 328, 584, 776, 176, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_333, vertices_214, vertices_666, vertices_898, vertices_620, vertices_244, vertices_696, vertices_840, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_265, vertices_321, vertices_22, vertices_70, vertices_26, vertices_522, vertices_146, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_52, vertices_212, vertices_100, vertices_56, vertices_664, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_333), (true, vertices_146), (true, vertices_642), (true, vertices_212), (true, vertices_100), (true, vertices_664), (true, vertices_552), (true, vertices_584), (true, vertices_176), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_212) then 18 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_664) then 20 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 19 => Sum.inl 2
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
cert_row_4 0 4 5 6 7 8 992 224 3
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_2 2 2 3 6 8 664
cert_row_2 3 1 3 5 6 212
cert_rows
cert_pivot_2 7 4 2 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 3 0 1 3 5 22 214 3
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 26 666 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 44 620 3
cert_coverFacet 4 244
cert_cover_5 4 3 1 3 4 5 52 244 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 992
cert_cover_5 7 0 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0117

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0118.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0118

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 333, 214, 538, 914, 108, 244, 696, 872, 992, 7, 11, 67, 259, 13, 69, 265, 321, 22, 70, 26, 522, 146, 530, 194, 386, 770, 44, 76, 52, 212, 100, 56, 536, 104, 552, 328, 776, 176, 656, 224, 864, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_333, vertices_214, vertices_538, vertices_914, vertices_108, vertices_244, vertices_696, vertices_872, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_265, vertices_321, vertices_22, vertices_70, vertices_26, vertices_522, vertices_146, vertices_530, vertices_194, vertices_386, vertices_770, vertices_44, vertices_76, vertices_52, vertices_212, vertices_100, vertices_56, vertices_536, vertices_104, vertices_552, vertices_328, vertices_776, vertices_176, vertices_656, vertices_224, vertices_864, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_333), (true, vertices_146), (true, vertices_530), (true, vertices_212), (true, vertices_100), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_864), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_212) then 18 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_864) then 22 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(true, vertices_864), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 6 212
cert_row_2 1 4 5 7 8 864
cert_row_4 2 0 3 6 7 8 914 146 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 914
cert_cover_5 2 2 0 3 6 7 146 914 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 52 244 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 872
cert_cover_5 6 1 2 4 5 7 104 872 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0118

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0119.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0119

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 333, 214, 666, 898, 812, 372, 696, 496, 928, 7, 11, 67, 259, 13, 69, 265, 321, 22, 70, 26, 522, 146, 194, 386, 642, 770, 44, 268, 52, 84, 292, 324, 56, 664, 552, 776, 368, 176, 208, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_333, vertices_214, vertices_666, vertices_898, vertices_812, vertices_372, vertices_696, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_265, vertices_321, vertices_22, vertices_70, vertices_26, vertices_522, vertices_146, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_84, vertices_292, vertices_324, vertices_56, vertices_664, vertices_552, vertices_776, vertices_368, vertices_176, vertices_208, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_333), (true, vertices_146), (true, vertices_642), (true, vertices_84), (true, vertices_292), (true, vertices_664), (true, vertices_552), (true, vertices_368), (true, vertices_176), (true, vertices_208), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_664) then 19 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_368) then 21 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
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
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 2 3 6 8 664
cert_row_2 2 3 4 5 7 368
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 0 6 3 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 26 666 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 812
cert_cover_5 3 3 1 2 4 7 44 812 3
cert_coverFacet 4 372
cert_cover_5 4 2 1 3 4 5 52 372 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 496
cert_cover_5 6 2 3 4 5 6 368 496 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0119

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0120.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0120

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 213, 809, 241, 353, 782, 454, 668, 900, 696, 992, 7, 11, 67, 21, 69, 41, 265, 49, 209, 97, 289, 321, 14, 70, 262, 266, 322, 28, 524, 148, 196, 388, 644, 772, 56, 664, 552, 776, 176, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_213, vertices_809, vertices_241, vertices_353, vertices_782, vertices_454, vertices_668, vertices_900, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_209, vertices_97, vertices_289, vertices_321, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_524, vertices_148, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_664, vertices_552, vertices_776, vertices_176, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_213), (false, vertices_809), (false, vertices_241), (false, vertices_353), (true, vertices_262), (true, vertices_524), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_664), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 14 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_664) then 16 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 8 664
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 0 1 5 6 7 454 70 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 3 2 0 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 0 1 2 3 6 28 668 3
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 696
cert_cover_5 4 0 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0120

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0121.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0121

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 213, 665, 897, 334, 364, 116, 824, 752, 992, 7, 11, 67, 259, 21, 69, 25, 521, 145, 193, 385, 641, 769, 14, 70, 266, 322, 44, 332, 52, 84, 100, 56, 536, 296, 776, 112, 560, 208, 656, 736, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_213, vertices_665, vertices_897, vertices_334, vertices_364, vertices_116, vertices_824, vertices_752, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_521, vertices_145, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_332, vertices_52, vertices_84, vertices_100, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_736, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_665), (false, vertices_897), (true, vertices_332), (true, vertices_100), (true, vertices_296), (true, vertices_112), (true, vertices_560), (true, vertices_736), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 17 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 9 else
  if p.val = (false, vertices_451) then 10 else
  if p.val = (false, vertices_213) then 13 else
  if p.val = (false, vertices_665) then 16 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_332) then 14 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_736) then 19 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_800) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 6 8 736
cert_row_2 1 1 2 5 7 332
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 1 6 2
cert_heightProof 3
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 14 334 3
cert_coverFacet 1 364
cert_cover_5 1 1 1 2 4 5 44 364 3
cert_coverFacet 2 116
cert_cover_2 2 3 1 4 5 52 116 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 752
cert_cover_5 4 0 3 4 5 6 112 752 3
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 7 736 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0121

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0122.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0122

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 661, 361, 817, 78, 454, 220, 900, 248, 688, 992, 7, 11, 259, 21, 517, 41, 329, 49, 529, 289, 769, 14, 70, 262, 74, 322, 28, 76, 148, 196, 388, 644, 772, 56, 216, 104, 176, 560, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_661, vertices_361, vertices_817, vertices_78, vertices_454, vertices_220, vertices_900, vertices_248, vertices_688, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_329, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_322, vertices_28, vertices_76, vertices_148, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_216, vertices_104, vertices_176, vertices_560, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_70), (true, vertices_76), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_176), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 17 14 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_661) then 13 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_216) then 16 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 0 2 4
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 28 220 3
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 688
cert_cover_2 5 4 3 6 8 176 688 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0122

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0123.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0123

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 533, 361, 689, 801, 78, 454, 220, 916, 248, 992, 7, 11, 259, 21, 517, 41, 329, 49, 529, 289, 545, 769, 14, 70, 262, 74, 322, 28, 76, 148, 532, 196, 388, 772, 56, 216, 104, 176, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_533, vertices_361, vertices_689, vertices_801, vertices_78, vertices_454, vertices_220, vertices_916, vertices_248, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_329, vertices_49, vertices_529, vertices_289, vertices_545, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_322, vertices_28, vertices_76, vertices_148, vertices_532, vertices_196, vertices_388, vertices_772, vertices_56, vertices_216, vertices_104, vertices_176, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_533), (false, vertices_361), (false, vertices_689), (false, vertices_801), (true, vertices_70), (true, vertices_76), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_224), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 17 14 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_689) then 15 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_216) then 16 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 2 0 1 4
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 28 220 3
cert_coverFacet 3 916
cert_cover_5 3 2 1 3 6 7 148 916 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0123

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0124.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0124

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 809, 241, 609, 782, 454, 834, 412, 440, 992, 7, 11, 67, 21, 69, 41, 521, 49, 209, 97, 545, 577, 14, 70, 262, 522, 322, 578, 770, 28, 268, 148, 196, 388, 56, 408, 296, 776, 176, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_809, vertices_241, vertices_609, vertices_782, vertices_454, vertices_834, vertices_412, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_545, vertices_577, vertices_14, vertices_70, vertices_262, vertices_522, vertices_322, vertices_578, vertices_770, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_809), (false, vertices_241), (false, vertices_609), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_408), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 14 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_408) then 16 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 0 1 5 6 7 454 70 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 3 2 0 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 28 412 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0124

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0125.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0125

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 213, 409, 590, 834, 620, 436, 484, 824, 864, 7, 11, 67, 259, 21, 69, 25, 265, 145, 193, 385, 14, 70, 522, 322, 578, 770, 44, 588, 52, 148, 100, 420, 196, 56, 280, 552, 776, 304, 400, 352, 608, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_213, vertices_409, vertices_590, vertices_834, vertices_620, vertices_436, vertices_484, vertices_824, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_522, vertices_322, vertices_578, vertices_770, vertices_44, vertices_588, vertices_52, vertices_148, vertices_100, vertices_420, vertices_196, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_352, vertices_608, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_409), (true, vertices_578), (true, vertices_588), (true, vertices_100), (true, vertices_420), (true, vertices_552), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 16 12 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 10 else
  if p.val = (false, vertices_451) then 11 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_409) then 14 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_588) then 15 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_420) then 18 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 6 7 420
cert_row_2 1 1 2 5 8 588
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 1 6 2
cert_heightProof 3
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 14 590 3
cert_coverFacet 1 834
cert_cover_2 1 5 0 7 8 322 834 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 436
cert_cover_5 3 0 1 3 4 6 52 436 3
cert_coverFacet 4 484
cert_cover_5 4 0 1 4 5 6 100 484 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0125

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0126.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0126

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 833, 214, 410, 620, 244, 696, 904, 992, 7, 11, 67, 259, 13, 69, 521, 321, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 588, 52, 212, 100, 56, 152, 552, 392, 648, 776, 176, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_833, vertices_214, vertices_410, vertices_620, vertices_244, vertices_696, vertices_904, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_588, vertices_52, vertices_212, vertices_100, vertices_56, vertices_152, vertices_552, vertices_392, vertices_648, vertices_776, vertices_176, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_833), (true, vertices_146), (true, vertices_212), (true, vertices_100), (true, vertices_152), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_176), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_212) then 19 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_2 3 1 2 5 8 588
cert_row_2 4 1 3 5 6 212
cert_rows_2
cert_pivot 0 7 4 2 1
cert_heightProof 5
cert_coverFacet 0 214
cert_cover_5 0 4 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 26 410 3
cert_coverFacet 2 620
cert_cover_5 2 3 1 2 4 5 44 620 3
cert_coverFacet 3 244
cert_cover_5 3 4 1 3 4 5 52 244 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0126

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0127.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0127

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 405, 617, 817, 78, 454, 834, 220, 248, 432, 992, 7, 11, 515, 21, 261, 41, 585, 49, 273, 545, 769, 14, 70, 262, 74, 322, 578, 770, 28, 76, 148, 196, 388, 56, 216, 104, 176, 304, 400, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_405, vertices_617, vertices_817, vertices_78, vertices_454, vertices_834, vertices_220, vertices_248, vertices_432, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_261, vertices_41, vertices_585, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_322, vertices_578, vertices_770, vertices_28, vertices_76, vertices_148, vertices_196, vertices_388, vertices_56, vertices_216, vertices_104, vertices_176, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_405), (false, vertices_617), (false, vertices_817), (true, vertices_70), (true, vertices_322), (true, vertices_76), (true, vertices_196), (true, vertices_216), (true, vertices_176), (true, vertices_224), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 17 14 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_405) then 13 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_216) then 16 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 0 2 4
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 28 220 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0127

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0128.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0128

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 523, 835, 213, 617, 241, 782, 454, 412, 440, 808, 992, 7, 11, 67, 515, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 522, 322, 770, 28, 268, 148, 196, 388, 56, 408, 296, 552, 776, 176, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_523, vertices_835, vertices_213, vertices_617, vertices_241, vertices_782, vertices_454, vertices_412, vertices_440, vertices_808, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_522, vertices_322, vertices_770, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_296, vertices_552, vertices_776, vertices_176, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_523), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_388), (true, vertices_408), (true, vertices_296), (true, vertices_776), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 14 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_523) then 1 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_617) then 15 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_408) then 16 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 0 1 5 6 7 454 70 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 3 2 0 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 28 412 3
cert_coverFacet 3 440
cert_cover_5 3 0 2 3 4 6 56 440 3
cert_coverFacet 4 808
cert_cover_2 4 4 2 7 8 296 808 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0128

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0129.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0129

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 833, 214, 538, 914, 620, 244, 696, 992, 7, 11, 67, 259, 13, 69, 521, 321, 577, 769, 22, 70, 26, 522, 146, 530, 194, 386, 770, 44, 588, 52, 212, 100, 56, 536, 552, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_833, vertices_214, vertices_538, vertices_914, vertices_620, vertices_244, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_522, vertices_146, vertices_530, vertices_194, vertices_386, vertices_770, vertices_44, vertices_588, vertices_52, vertices_212, vertices_100, vertices_56, vertices_536, vertices_552, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_833), (true, vertices_146), (true, vertices_530), (true, vertices_212), (true, vertices_100), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_212) then 19 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 8 914 146 3
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_2 3 1 2 5 8 588
cert_row_2 4 1 3 5 6 212
cert_rows_2
cert_pivot 0 7 4 2 1
cert_heightProof 5
cert_coverFacet 0 214
cert_cover_5 0 4 0 1 3 5 22 214 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 914
cert_cover_5 2 0 0 3 6 7 146 914 3
cert_coverFacet 3 620
cert_cover_5 3 3 1 2 4 5 44 620 3
cert_coverFacet 4 244
cert_cover_5 4 4 1 3 4 5 52 244 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0129

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0130.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0130

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 525, 837, 214, 666, 898, 620, 244, 696, 992, 7, 11, 67, 259, 13, 69, 517, 521, 321, 769, 22, 70, 26, 522, 146, 194, 386, 642, 770, 44, 524, 52, 212, 100, 580, 56, 664, 552, 176, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_525, vertices_837, vertices_214, vertices_666, vertices_898, vertices_620, vertices_244, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_517, vertices_521, vertices_321, vertices_769, vertices_22, vertices_70, vertices_26, vertices_522, vertices_146, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_212, vertices_100, vertices_580, vertices_56, vertices_664, vertices_552, vertices_176, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_525), (false, vertices_837), (true, vertices_146), (true, vertices_642), (true, vertices_212), (true, vertices_100), (true, vertices_664), (true, vertices_552), (true, vertices_176), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_212) then 17 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_664) then 19 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 4 5 6 7 8 992 224 3
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_2 2 2 3 6 8 664
cert_row_2 3 1 3 5 6 212
cert_rows
cert_pivot_2 7 4 2 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 3 0 1 3 5 22 214 3
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 26 666 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 44 620 3
cert_coverFacet 4 244
cert_cover_5 4 3 1 3 4 5 52 244 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0130

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0131.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0131

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 523, 835, 85, 681, 625, 782, 454, 220, 908, 248, 992, 7, 11, 67, 515, 21, 69, 41, 521, 49, 81, 545, 577, 14, 70, 262, 522, 322, 770, 28, 140, 780, 84, 196, 388, 56, 216, 168, 648, 112, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_523, vertices_835, vertices_85, vertices_681, vertices_625, vertices_782, vertices_454, vertices_220, vertices_908, vertices_248, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_70, vertices_262, vertices_522, vertices_322, vertices_770, vertices_28, vertices_140, vertices_780, vertices_84, vertices_196, vertices_388, vertices_56, vertices_216, vertices_168, vertices_648, vertices_112, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_523), (false, vertices_835), (false, vertices_85), (false, vertices_681), (false, vertices_625), (true, vertices_262), (true, vertices_140), (true, vertices_780), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_224), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_523) then 1 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_85) then 2 else
  if p.val = (false, vertices_681) then 16 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_780) then 14 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_216) then 17 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_2 1 1 2 7 8 780
cert_row_4 2 0 1 5 6 7 454 70 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 3 2 0 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 28 220 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 140 908 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0131

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0132.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0132

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 523, 835, 213, 617, 241, 782, 454, 156, 908, 696, 992, 7, 11, 67, 515, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 522, 322, 770, 28, 140, 780, 148, 196, 388, 56, 152, 552, 648, 176, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_523, vertices_835, vertices_213, vertices_617, vertices_241, vertices_782, vertices_454, vertices_156, vertices_908, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_522, vertices_322, vertices_770, vertices_28, vertices_140, vertices_780, vertices_148, vertices_196, vertices_388, vertices_56, vertices_152, vertices_552, vertices_648, vertices_176, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_523), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_140), (true, vertices_780), (true, vertices_388), (true, vertices_152), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_523) then 1 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_780) then 14 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 2 7 8 780
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 908
cert_cover_5 3 1 1 2 6 7 140 908 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0132

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0133.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0133

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 75, 835, 533, 617, 689, 78, 454, 220, 916, 248, 992, 7, 11, 67, 771, 21, 517, 41, 73, 49, 529, 545, 577, 14, 70, 262, 74, 322, 28, 76, 148, 532, 196, 388, 772, 56, 216, 104, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_75, vertices_835, vertices_533, vertices_617, vertices_689, vertices_78, vertices_454, vertices_220, vertices_916, vertices_248, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_517, vertices_41, vertices_73, vertices_49, vertices_529, vertices_545, vertices_577, vertices_14, vertices_70, vertices_262, vertices_74, vertices_322, vertices_28, vertices_76, vertices_148, vertices_532, vertices_196, vertices_388, vertices_772, vertices_56, vertices_216, vertices_104, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_75), (false, vertices_835), (false, vertices_533), (false, vertices_617), (false, vertices_689), (true, vertices_70), (true, vertices_76), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_224), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_216) then 17 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 2 0 1 4
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 28 220 3
cert_coverFacet 3 916
cert_cover_5 3 2 1 3 6 7 148 916 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0133

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0750 : Certifies 750 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0102.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0751 : Certifies 751 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0103.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0752 : Certifies 752 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0106.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0753 : Certifies 753 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0107.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0754 : Certifies 754 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0108.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0755 : Certifies 755 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0109.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0756 : Certifies 756 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0110.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0757 : Certifies 757 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0111.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0758 : Certifies 758 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0112.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0759 : Certifies 759 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0113.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0760 : Certifies 760 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0114.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0761 : Certifies 761 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0115.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0762 : Certifies 762 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0116.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0763 : Certifies 763 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0117.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0764 : Certifies 764 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0118.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0765 : Certifies 765 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0119.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0766 : Certifies 766 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0120.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0767 : Certifies 767 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0121.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0768 : Certifies 768 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0122.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0769 : Certifies 769 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0123.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0770 : Certifies 770 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0124.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0771 : Certifies 771 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0125.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0772 : Certifies 772 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0126.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0773 : Certifies 773 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0127.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0774 : Certifies 774 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0128.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0775 : Certifies 775 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0129.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0776 : Certifies 776 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0130.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0777 : Certifies 777 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0131.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0778 : Certifies 778 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0132.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0779 : Certifies 779 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0133.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B025 (j : Fin 30) :
    Certifies (750 + j.val) := by
  fin_cases j
  · exact projection_0750
  · exact projection_0751
  · exact projection_0752
  · exact projection_0753
  · exact projection_0754
  · exact projection_0755
  · exact projection_0756
  · exact projection_0757
  · exact projection_0758
  · exact projection_0759
  · exact projection_0760
  · exact projection_0761
  · exact projection_0762
  · exact projection_0763
  · exact projection_0764
  · exact projection_0765
  · exact projection_0766
  · exact projection_0767
  · exact projection_0768
  · exact projection_0769
  · exact projection_0770
  · exact projection_0771
  · exact projection_0772
  · exact projection_0773
  · exact projection_0774
  · exact projection_0775
  · exact projection_0776
  · exact projection_0777
  · exact projection_0778
  · exact projection_0779

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
