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
/- Source: ProjectionCertificates/R_one_six_1365.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1365

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 364, 612, 676, 440, 344, 992, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 76, 100, 164, 548, 580, 644, 56, 88, 280, 296, 328, 176, 336, 400, 352, 608, 416, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_364, vertices_612, vertices_676, vertices_440, vertices_344, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_76, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_76), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_608), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 337 1 76 100 548 580 280 296 328 352 608 416 672 647 181 63 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 5 7 364 44 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 364
cert_cover_5 1 1 1 2 4 5 44 364 3
cert_coverFacet 2 612
cert_cover_2 2 4 1 5 8 100 612 3
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1365

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1366.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1366

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 364, 228, 708, 440, 344, 992, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 76, 100, 164, 196, 580, 644, 56, 88, 280, 296, 328, 176, 336, 400, 224, 352, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_364, vertices_228, vertices_708, vertices_440, vertices_344, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_76, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_76), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 337 1 76 100 196 580 280 296 328 224 352 416 704 647 181 63 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 5 7 364 44 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 364
cert_cover_5 1 1 1 2 4 5 44 364 3
cert_coverFacet 2 228
cert_cover_2 2 4 1 5 6 100 228 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1366

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1367.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1367

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 361, 737, 94, 838, 340, 916, 440, 344, 480, 960, 7, 11, 515, 53, 133, 41, 73, 97, 161, 577, 641, 30, 70, 518, 74, 578, 84, 148, 276, 324, 644, 772, 56, 88, 280, 296, 328, 176, 336, 400, 224, 352, 416, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_737, vertices_94, vertices_838, vertices_340, vertices_916, vertices_440, vertices_344, vertices_480, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_97, vertices_161, vertices_577, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_737), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_336), (true, vertices_400), (true, vertices_416), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 70 3
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 340
cert_cover_2 2 3 1 5 7 84 340 3
cert_coverFacet 3 916
cert_cover_5 3 2 1 3 6 7 148 916 3
cert_coverFacet 4 440
cert_cover_5 4 3 2 3 4 6 56 440 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 480
cert_cover_2 6 5 4 6 7 224 480 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1367

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1368.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1368

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 361, 737, 94, 838, 340, 916, 440, 344, 864, 928, 7, 11, 515, 53, 133, 41, 73, 97, 161, 577, 641, 30, 70, 518, 74, 578, 84, 148, 276, 324, 644, 772, 56, 88, 280, 296, 328, 176, 336, 400, 352, 608, 416, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_737, vertices_94, vertices_838, vertices_340, vertices_916, vertices_440, vertices_344, vertices_864, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_97, vertices_161, vertices_577, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_737), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_336), (true, vertices_400), (true, vertices_416), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 70 3
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 340
cert_cover_2 2 3 1 5 7 84 340 3
cert_coverFacet 3 916
cert_cover_5 3 2 1 3 6 7 148 916 3
cert_coverFacet 4 440
cert_cover_5 4 3 2 3 4 6 56 440 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1368

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1369.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1369

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 361, 929, 833, 94, 838, 340, 916, 248, 464, 480, 7, 11, 515, 53, 133, 41, 73, 161, 289, 321, 577, 641, 769, 30, 70, 518, 74, 578, 84, 148, 276, 324, 644, 772, 56, 88, 104, 176, 208, 336, 400, 224, 352, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_929, vertices_833, vertices_94, vertices_838, vertices_340, vertices_916, vertices_248, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_929), (false, vertices_833), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 6 248 56 3
cert_row_2 1 0 1 2 3 30
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 838
cert_cover_5 1 2 0 1 5 7 70 838 3
cert_coverFacet 2 340
cert_cover_2 2 3 1 5 7 84 340 3
cert_coverFacet 3 916
cert_cover_5 3 3 1 3 6 7 148 916 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 464
cert_cover_2 5 5 3 6 7 208 464 3
cert_coverFacet 6 480
cert_cover_2 6 5 4 6 7 224 480 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1369

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1370.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1370

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 364, 932, 836, 184, 472, 424, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 76, 164, 292, 324, 580, 644, 772, 56, 88, 152, 168, 296, 328, 392, 176, 336, 400, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_364, vertices_932, vertices_836, vertices_184, vertices_472, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_76, vertices_164, vertices_292, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_168, vertices_296, vertices_328, vertices_392, vertices_176, vertices_336, vertices_400, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_76), (true, vertices_292), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 337 1 76 292 324 580 772 152 168 296 328 392 416 647 181 63 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 4 6 7 8 932 164 3
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 364
cert_cover_5 1 2 1 2 4 5 44 364 3
cert_coverFacet 2 932
cert_cover_5 2 1 1 4 6 7 164 932 3
cert_coverFacet 3 836
cert_cover_2 3 5 1 7 8 324 836 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 88 472 3
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1370

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1371.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1371

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 181, 361, 929, 94, 838, 330, 340, 916, 248, 464, 480, 7, 11, 515, 53, 133, 41, 265, 161, 289, 641, 769, 30, 70, 518, 74, 266, 322, 770, 84, 148, 276, 324, 644, 772, 56, 88, 104, 328, 176, 208, 336, 400, 224, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_181, vertices_361, vertices_929, vertices_94, vertices_838, vertices_330, vertices_340, vertices_916, vertices_248, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_265, vertices_161, vertices_289, vertices_641, vertices_769, vertices_30, vertices_70, vertices_518, vertices_74, vertices_266, vertices_322, vertices_770, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_328, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_181), (false, vertices_361), (false, vertices_929), (true, vertices_70), (true, vertices_74), (true, vertices_322), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_448) then 12 else
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
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 6 248 56 3
cert_row_2 1 0 1 2 3 30
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 838
cert_cover_5 1 2 0 1 5 7 70 838 3
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 340
cert_cover_2 3 3 1 5 7 84 340 3
cert_coverFacet 4 916
cert_cover_5 4 3 1 3 6 7 148 916 3
cert_coverFacet 5 248
cert_cover_5 5 0 2 3 4 5 56 248 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1371

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1373.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1373

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 654, 86, 582, 202, 962, 692, 852, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 70, 518, 74, 138, 82, 194, 578, 642, 140, 52, 84, 532, 164, 580, 644, 200, 304, 560, 336, 784, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_86, vertices_582, vertices_202, vertices_962, vertices_692, vertices_852, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_84, vertices_532, vertices_164, vertices_580, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_70), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_644), (true, vertices_560), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 2 0 4 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 194 962 3
cert_coverFacet 5 692
cert_cover_5 5 2 1 3 4 6 52 692 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 84 852 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1373

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1374.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1374

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 433, 849, 654, 86, 582, 202, 962, 628, 932, 816, 27, 45, 73, 137, 49, 81, 273, 161, 321, 385, 14, 22, 70, 518, 74, 138, 82, 194, 578, 642, 140, 52, 84, 164, 548, 580, 644, 200, 304, 560, 592, 784, 416, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_433, vertices_849, vertices_654, vertices_86, vertices_582, vertices_202, vertices_962, vertices_628, vertices_932, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_273, vertices_161, vertices_321, vertices_385, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_84, vertices_164, vertices_548, vertices_580, vertices_644, vertices_200, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_433), (false, vertices_849), (true, vertices_70), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_84), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_560), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 194 962 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 52 628 3
cert_coverFacet 6 932
cert_cover_5 6 3 1 4 6 7 164 932 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1374

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1375.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1375

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 654, 342, 774, 202, 962, 692, 788, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 262, 518, 74, 138, 82, 194, 322, 642, 770, 140, 52, 276, 532, 164, 644, 772, 200, 304, 560, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_342, vertices_774, vertices_202, vertices_962, vertices_692, vertices_788, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_322, vertices_642, vertices_770, vertices_140, vertices_52, vertices_276, vertices_532, vertices_164, vertices_644, vertices_772, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 0 1 3 5 7 342 22 3
cert_row_4 3 0 5 6 7 8 962 194 3
cert_rows
cert_pivot_2 2 4 1 0
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
cert_cover_5 4 3 0 5 6 7 194 962 3
cert_coverFacet 5 692
cert_cover_5 5 1 1 3 4 6 52 692 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1375

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1376.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1376

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 59, 787, 141, 901, 425, 369, 126, 662, 236, 212, 720, 848, 992, 11, 19, 515, 13, 133, 517, 41, 137, 49, 273, 289, 385, 769, 14, 22, 518, 58, 530, 108, 140, 84, 148, 196, 644, 168, 112, 208, 336, 592, 656, 784, 224, 352, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_59, vertices_787, vertices_141, vertices_901, vertices_425, vertices_369, vertices_126, vertices_662, vertices_236, vertices_212, vertices_720, vertices_848, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_515, vertices_13, vertices_133, vertices_517, vertices_41, vertices_137, vertices_49, vertices_273, vertices_289, vertices_385, vertices_769, vertices_14, vertices_22, vertices_518, vertices_58, vertices_530, vertices_108, vertices_140, vertices_84, vertices_148, vertices_196, vertices_644, vertices_168, vertices_112, vertices_208, vertices_336, vertices_592, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_59), (false, vertices_787), (false, vertices_141), (false, vertices_901), (false, vertices_425), (false, vertices_369), (true, vertices_22), (true, vertices_108), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_224), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 12 else
  if p.val = (false, vertices_59) then 13 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 4 5 6 7 8 992 224 3
cert_row_4 1 0 1 2 3 4 126 14 3
cert_row_4 2 0 1 2 3 5 126 14 3
cert_row_4 3 0 1 3 6 8 662 22 3
cert_rows
cert_pivot_2 7 4 2 0
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 662
cert_cover_5 1 3 0 1 3 6 22 662 3
cert_coverFacet 2 236
cert_cover 2 4 1 1 2 3 0 6 2 108 236 108 14 126 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 720
cert_cover_2 4 5 3 6 8 208 720 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1376

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1377.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1377

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 590, 790, 338, 962, 204, 692, 708, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 82, 274, 322, 578, 770, 76, 140, 52, 532, 164, 196, 580, 644, 200, 304, 560, 336, 784, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_590, vertices_790, vertices_338, vertices_962, vertices_204, vertices_692, vertices_708, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_52, vertices_532, vertices_164, vertices_196, vertices_580, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_76), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_560), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 322 962 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1377

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1379.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1379

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 590, 790, 338, 962, 652, 692, 712, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 82, 274, 322, 578, 770, 140, 524, 52, 532, 164, 644, 200, 584, 648, 304, 560, 336, 784, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_590, vertices_790, vertices_338, vertices_962, vertices_652, vertices_692, vertices_712, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_140, vertices_524, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 322 962 2
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1379

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1383.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1383

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 526, 790, 586, 338, 962, 716, 692, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 522, 82, 274, 322, 578, 770, 140, 524, 52, 532, 164, 644, 200, 584, 304, 560, 336, 784, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_526, vertices_790, vertices_586, vertices_338, vertices_962, vertices_716, vertices_692, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_522, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_140, vertices_524, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_584, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_522), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_584), (true, vertices_560), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 8 716 140 2
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 322 962 2
cert_coverFacet 5 716
cert_cover_5 5 0 1 2 5 6 140 716 2
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1383

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1384.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1384

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 78, 790, 582, 338, 962, 716, 692, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 70, 518, 74, 82, 274, 322, 578, 770, 76, 140, 52, 532, 164, 580, 644, 200, 304, 560, 336, 784, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_78, vertices_790, vertices_582, vertices_338, vertices_962, vertices_716, vertices_692, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_52, vertices_532, vertices_164, vertices_580, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_70), (true, vertices_518), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_76), (true, vertices_532), (true, vertices_580), (true, vertices_644), (true, vertices_560), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 8 716 76 3
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 962
cert_cover_5 4 1 0 5 6 7 322 962 2
cert_coverFacet 5 716
cert_cover_5 5 0 1 2 5 6 76 716 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 52 692 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1384

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1385.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1385

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [139, 779, 659, 837, 425, 737, 353, 126, 270, 790, 186, 364, 724, 240, 11, 131, 515, 137, 265, 97, 161, 289, 321, 577, 641, 769, 14, 22, 262, 58, 138, 266, 146, 530, 770, 108, 268, 84, 532, 324, 580, 772, 168, 296, 112, 176, 208, 656, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_139, vertices_779, vertices_659, vertices_837, vertices_425, vertices_737, vertices_353, vertices_126, vertices_270, vertices_790, vertices_186, vertices_364, vertices_724, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_515, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_58, vertices_138, vertices_266, vertices_146, vertices_530, vertices_770, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_208, vertices_656, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_139), (false, vertices_779), (false, vertices_659), (false, vertices_837), (false, vertices_425), (false, vertices_737), (false, vertices_353), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_58), (true, vertices_108), (true, vertices_268), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_176), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_262) then 4 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 14 3
cert_row_4 1 0 1 2 3 5 126 14 3
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 790
cert_cover_5 2 2 0 1 3 7 22 790 3
cert_coverFacet 3 186
cert_cover 3 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 4 364
cert_cover 4 4 1 1 2 3 0 7 2 108 364 108 14 126 3
cert_coverFacet 5 724
cert_cover_5 5 3 1 3 5 6 84 724 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1385

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1386.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1386

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 181, 901, 465, 654, 774, 842, 172, 632, 680, 944, 848, 7, 27, 67, 53, 133, 261, 81, 145, 321, 385, 14, 262, 518, 74, 522, 322, 770, 44, 140, 164, 644, 772, 56, 88, 168, 552, 584, 648, 176, 560, 336, 592, 400, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_181, vertices_901, vertices_465, vertices_654, vertices_774, vertices_842, vertices_172, vertices_632, vertices_680, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_770, vertices_44, vertices_140, vertices_164, vertices_644, vertices_772, vertices_56, vertices_88, vertices_168, vertices_552, vertices_584, vertices_648, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_518), (true, vertices_522), (true, vertices_770), (true, vertices_140), (true, vertices_168), (true, vertices_552), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 0 518 1 522 770 140 168 552 584 648 560 592 784 672 832 327 91 63 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1386

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1387.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1387

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 181, 901, 465, 654, 774, 842, 172, 376, 680, 808, 944, 7, 27, 67, 53, 133, 261, 81, 145, 321, 385, 14, 262, 518, 74, 522, 322, 770, 44, 140, 164, 644, 772, 56, 88, 168, 296, 552, 328, 648, 776, 176, 304, 336, 400, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_181, vertices_901, vertices_465, vertices_654, vertices_774, vertices_842, vertices_172, vertices_376, vertices_680, vertices_808, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_770, vertices_44, vertices_140, vertices_164, vertices_644, vertices_772, vertices_56, vertices_88, vertices_168, vertices_296, vertices_552, vertices_328, vertices_648, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_518), (true, vertices_522), (true, vertices_770), (true, vertices_140), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 0 518 1 522 770 140 168 296 552 328 648 776 304 672 800 327 91 63 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1387

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1388.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1388

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 181, 901, 465, 833, 654, 842, 172, 376, 680, 808, 944, 7, 27, 67, 53, 133, 517, 81, 145, 321, 577, 385, 769, 14, 518, 74, 522, 578, 44, 140, 164, 644, 56, 88, 168, 296, 552, 328, 648, 776, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_181, vertices_901, vertices_465, vertices_833, vertices_654, vertices_842, vertices_172, vertices_376, vertices_680, vertices_808, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_522, vertices_578, vertices_44, vertices_140, vertices_164, vertices_644, vertices_56, vertices_88, vertices_168, vertices_296, vertices_552, vertices_328, vertices_648, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (false, vertices_833), (true, vertices_522), (true, vertices_140), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_583) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 1 833 0 522 140 168 296 552 328 648 776 304 672 800 583 91 63 181 901 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 74 842 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 680
cert_cover_2 4 4 2 6 8 168 680 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1388

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1389.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1389

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 654, 86, 582, 842, 692, 852, 904, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 70, 518, 74, 522, 82, 578, 140, 52, 84, 532, 164, 580, 644, 328, 392, 648, 776, 304, 560, 336, 784, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_86, vertices_582, vertices_842, vertices_692, vertices_852, vertices_904, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_522, vertices_82, vertices_578, vertices_140, vertices_52, vertices_84, vertices_532, vertices_164, vertices_580, vertices_644, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_578), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_644), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 8 692 52 3
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 0 2 5 7 8 842 74 3
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 74 842 3
cert_coverFacet 4 692
cert_cover_5 4 0 1 3 4 6 52 692 3
cert_coverFacet 5 852
cert_cover_5 5 3 1 3 5 7 84 852 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1389

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1390.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1390

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 654, 586, 898, 620, 676, 376, 944, 864, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 134, 74, 522, 578, 386, 642, 770, 44, 524, 164, 548, 644, 56, 88, 104, 584, 176, 304, 336, 400, 352, 608, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_654, vertices_586, vertices_898, vertices_620, vertices_676, vertices_376, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_134, vertices_74, vertices_522, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_104, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_522), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_644), (true, vertices_104), (true, vertices_584), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 1 522 0 642 524 548 644 104 584 304 352 608 672 800 896 391 181 63 91 835 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 44 620 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 376
cert_cover_5 5 2 2 3 4 5 56 376 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1390

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1391.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1391

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 142, 598, 902, 842, 394, 692, 816, 848, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 134, 518, 74, 138, 266, 82, 578, 386, 770, 140, 52, 532, 164, 644, 328, 392, 304, 560, 336, 592, 784, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_142, vertices_598, vertices_902, vertices_842, vertices_394, vertices_692, vertices_816, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_134, vertices_518, vertices_74, vertices_138, vertices_266, vertices_82, vertices_578, vertices_386, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_328, vertices_392, vertices_304, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 134 902 3
cert_coverFacet 3 842
cert_cover_5 3 0 0 2 5 7 74 842 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1391

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1392.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1392

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 142, 598, 902, 842, 394, 692, 624, 864, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 134, 518, 74, 138, 266, 82, 578, 386, 770, 140, 52, 532, 164, 644, 328, 392, 112, 560, 592, 352, 608, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_142, vertices_598, vertices_902, vertices_842, vertices_394, vertices_692, vertices_624, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_134, vertices_518, vertices_74, vertices_138, vertices_266, vertices_82, vertices_578, vertices_386, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_328, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 134 902 3
cert_coverFacet 3 842
cert_cover_5 3 0 0 2 5 7 74 842 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1392

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1393.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1393

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 267, 425, 721, 225, 865, 126, 270, 662, 186, 364, 852, 240, 11, 259, 515, 137, 265, 97, 161, 289, 193, 577, 641, 769, 14, 22, 262, 518, 58, 138, 266, 146, 642, 108, 268, 84, 532, 324, 772, 168, 296, 112, 176, 208, 592, 656, 224, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_267, vertices_425, vertices_721, vertices_225, vertices_865, vertices_126, vertices_270, vertices_662, vertices_186, vertices_364, vertices_852, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_58, vertices_138, vertices_266, vertices_146, vertices_642, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_267), (false, vertices_425), (false, vertices_721), (false, vertices_225), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_108), (true, vertices_268), (true, vertices_84), (true, vertices_532), (true, vertices_324), (true, vertices_112), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 17 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_108) then 16 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 14 3
cert_row_4 1 0 1 2 3 5 126 14 3
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 186
cert_cover 3 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 4 364
cert_cover 4 4 1 1 2 3 0 7 2 108 364 108 14 126 3
cert_coverFacet 5 852
cert_cover_5 5 3 1 3 5 7 84 852 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1393

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1394.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1394

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 267, 425, 113, 177, 721, 865, 126, 270, 662, 186, 364, 852, 11, 259, 515, 137, 265, 49, 81, 145, 97, 161, 289, 577, 641, 769, 14, 22, 262, 518, 58, 138, 266, 146, 642, 108, 268, 84, 532, 324, 772, 168, 296, 112, 176, 592, 656, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_267, vertices_425, vertices_113, vertices_177, vertices_721, vertices_865, vertices_126, vertices_270, vertices_662, vertices_186, vertices_364, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_137, vertices_265, vertices_49, vertices_81, vertices_145, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_58, vertices_138, vertices_266, vertices_146, vertices_642, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_592, vertices_656, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_267), (false, vertices_425), (false, vertices_113), (false, vertices_177), (false, vertices_721), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_108), (true, vertices_268), (true, vertices_84), (true, vertices_532), (true, vertices_324)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_177) then 2 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (false, vertices_865) then 21 else
  if p.val = (true, vertices_14) then 3 else
  if p.val = (true, vertices_22) then 4 else
  if p.val = (true, vertices_58) then 13 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_108) then 15 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_324) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 14 3
cert_row_4 1 0 1 2 3 5 126 14 3
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 662
cert_cover_5 2 2 0 1 3 6 22 662 3
cert_coverFacet 3 186
cert_cover 3 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 4 364
cert_cover 4 4 1 1 2 3 0 7 2 108 364 108 14 126 3
cert_coverFacet 5 852
cert_cover_5 5 3 1 3 5 7 84 852 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1394

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1395.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1395

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 270, 598, 902, 842, 396, 692, 816, 848, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 262, 518, 74, 266, 82, 578, 770, 140, 268, 52, 532, 164, 388, 644, 328, 392, 304, 560, 336, 592, 784, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_270, vertices_598, vertices_902, vertices_842, vertices_396, vertices_692, vertices_816, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_266, vertices_82, vertices_578, vertices_770, vertices_140, vertices_268, vertices_52, vertices_532, vertices_164, vertices_388, vertices_644, vertices_328, vertices_392, vertices_304, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_4 2 0 1 6 7 8 902 262 2
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 262 902 2
cert_coverFacet 3 842
cert_cover_5 3 0 0 2 5 7 74 842 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1395

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1396.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1396

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 270, 598, 902, 842, 396, 692, 624, 864, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 262, 518, 74, 266, 82, 578, 770, 140, 268, 52, 532, 164, 388, 644, 328, 392, 112, 560, 592, 352, 608, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_270, vertices_598, vertices_902, vertices_842, vertices_396, vertices_692, vertices_624, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_266, vertices_82, vertices_578, vertices_770, vertices_140, vertices_268, vertices_52, vertices_532, vertices_164, vertices_388, vertices_644, vertices_328, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_4 2 0 1 6 7 8 902 262 2
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 598
cert_cover_5 1 1 0 1 3 5 22 598 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 262 902 2
cert_coverFacet 3 842
cert_cover_5 3 0 0 2 5 7 74 842 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 692
cert_cover_5 5 3 1 3 4 6 52 692 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1396

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1397.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1397

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 775, 651, 269, 425, 113, 177, 721, 865, 126, 662, 186, 364, 852, 7, 11, 515, 13, 261, 137, 265, 49, 81, 145, 97, 161, 289, 577, 641, 769, 14, 22, 518, 58, 138, 146, 642, 108, 268, 84, 532, 324, 772, 168, 296, 112, 176, 592, 656, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_775, vertices_651, vertices_269, vertices_425, vertices_113, vertices_177, vertices_721, vertices_865, vertices_126, vertices_662, vertices_186, vertices_364, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_13, vertices_261, vertices_137, vertices_265, vertices_49, vertices_81, vertices_145, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_518, vertices_58, vertices_138, vertices_146, vertices_642, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_592, vertices_656, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_775), (false, vertices_651), (false, vertices_269), (false, vertices_425), (false, vertices_113), (false, vertices_177), (false, vertices_721), (false, vertices_865), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_108), (true, vertices_84), (true, vertices_532), (true, vertices_324)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 13 15 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_651) then 11 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_425) then 16 else
  if p.val = (false, vertices_113) then 2 else
  if p.val = (false, vertices_177) then 3 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (false, vertices_865) then 20 else
  if p.val = (true, vertices_22) then 4 else
  if p.val = (true, vertices_58) then 12 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_108) then 14 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 3 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
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
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 186
cert_cover 2 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 3 364
cert_cover 3 4 1 1 2 3 0 7 2 108 364 108 14 126 3
cert_coverFacet 4 852
cert_cover_5 4 3 1 3 5 7 84 852 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1397

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1398.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1398

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 590, 774, 684, 900, 376, 808, 840, 944, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 262, 518, 74, 578, 770, 44, 524, 164, 388, 644, 772, 56, 88, 296, 552, 328, 584, 776, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_774, vertices_684, vertices_900, vertices_376, vertices_808, vertices_840, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_578, vertices_770, vertices_44, vertices_524, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_524), (true, vertices_644), (true, vertices_772), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
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
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 1 518 0 524 644 772 296 552 328 584 776 304 672 800 896 391 181 63 91 835 465
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
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1398

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1399.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1399

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 590, 774, 684, 900, 376, 616, 944, 864, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 262, 518, 74, 578, 770, 44, 524, 164, 388, 644, 772, 56, 88, 104, 552, 584, 176, 304, 336, 400, 352, 608, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_774, vertices_684, vertices_900, vertices_376, vertices_616, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_578, vertices_770, vertices_44, vertices_524, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_524), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
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
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_772) then 3 else
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
cert_nodeAtPriority_30 1 518 0 524 644 772 104 552 584 304 352 608 672 800 896 391 181 63 91 835 465
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
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1399

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1590 : Certifies 1590 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1365.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1591 : Certifies 1591 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1366.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1592 : Certifies 1592 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1367.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1593 : Certifies 1593 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1368.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1594 : Certifies 1594 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1369.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1595 : Certifies 1595 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1370.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1596 : Certifies 1596 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1371.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1597 : Certifies 1597 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1373.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1598 : Certifies 1598 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1374.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1599 : Certifies 1599 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1375.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1600 : Certifies 1600 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1376.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1601 : Certifies 1601 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1377.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1602 : Certifies 1602 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1379.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1603 : Certifies 1603 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1383.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1604 : Certifies 1604 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1384.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1605 : Certifies 1605 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1385.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1606 : Certifies 1606 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1386.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1607 : Certifies 1607 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1387.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1608 : Certifies 1608 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1388.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1609 : Certifies 1609 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1389.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1610 : Certifies 1610 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1390.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1611 : Certifies 1611 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1391.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1612 : Certifies 1612 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1392.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1613 : Certifies 1613 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1393.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1614 : Certifies 1614 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1394.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1615 : Certifies 1615 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1395.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1616 : Certifies 1616 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1396.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1617 : Certifies 1617 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1397.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1618 : Certifies 1618 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1398.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1619 : Certifies 1619 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1399.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B053 (j : Fin 30) :
    Certifies (1590 + j.val) := by
  fin_cases j
  · exact projection_1590
  · exact projection_1591
  · exact projection_1592
  · exact projection_1593
  · exact projection_1594
  · exact projection_1595
  · exact projection_1596
  · exact projection_1597
  · exact projection_1598
  · exact projection_1599
  · exact projection_1600
  · exact projection_1601
  · exact projection_1602
  · exact projection_1603
  · exact projection_1604
  · exact projection_1605
  · exact projection_1606
  · exact projection_1607
  · exact projection_1608
  · exact projection_1609
  · exact projection_1610
  · exact projection_1611
  · exact projection_1612
  · exact projection_1613
  · exact projection_1614
  · exact projection_1615
  · exact projection_1616
  · exact projection_1617
  · exact projection_1618
  · exact projection_1619

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
