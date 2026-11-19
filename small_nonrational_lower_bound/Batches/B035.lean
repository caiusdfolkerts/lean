module
public meta import LowerSchemas.Batches
public meta import ProjectionVertexSets
public import TerminalGeometry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Papers.FiniteProjectionChecks

section
set_option debug.skipKernelTC false
set_option profiler true
set_option profiler.threshold 250

section BundlePart0
/- Source: ProjectionCertificates/R_one_six_0522.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0522

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 835, 589, 406, 282, 450, 108, 244, 824, 744, 944, 960, 7, 11, 67, 771, 13, 69, 521, 577, 22, 134, 26, 266, 274, 194, 322, 386, 44, 76, 52, 148, 100, 196, 56, 280, 104, 552, 584, 776, 176, 816, 400, 224, 672, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_835, vertices_589, vertices_406, vertices_282, vertices_450, vertices_108, vertices_244, vertices_824, vertices_744, vertices_944, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_13, vertices_69, vertices_521, vertices_577, vertices_22, vertices_134, vertices_26, vertices_266, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_76, vertices_52, vertices_148, vertices_100, vertices_196, vertices_56, vertices_280, vertices_104, vertices_552, vertices_584, vertices_776, vertices_176, vertices_816, vertices_400, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_835), (false, vertices_589), (true, vertices_274), (true, vertices_386), (true, vertices_148), (true, vertices_100), (true, vertices_280), (true, vertices_104), (true, vertices_552), (true, vertices_176), (true, vertices_816), (true, vertices_400), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_816) then 23 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
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
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
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
cert_coverFacet 8 960
cert_cover_2 8 6 5 7 8 448 960 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0522

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0523.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0523

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 835, 589, 406, 282, 450, 108, 244, 696, 920, 616, 992, 7, 11, 67, 771, 13, 69, 521, 577, 22, 134, 26, 266, 274, 194, 322, 386, 44, 76, 52, 148, 100, 196, 56, 664, 280, 104, 552, 584, 776, 176, 400, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_835, vertices_589, vertices_406, vertices_282, vertices_450, vertices_108, vertices_244, vertices_696, vertices_920, vertices_616, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_13, vertices_69, vertices_521, vertices_577, vertices_22, vertices_134, vertices_26, vertices_266, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_76, vertices_52, vertices_148, vertices_100, vertices_196, vertices_56, vertices_664, vertices_280, vertices_104, vertices_552, vertices_584, vertices_776, vertices_176, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_835), (false, vertices_589), (true, vertices_274), (true, vertices_386), (true, vertices_148), (true, vertices_100), (true, vertices_664), (true, vertices_280), (true, vertices_104), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_664) then 22 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 8 664
cert_row_4 1 0 1 3 6 7 406 22 3
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 2 0 1 4
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 22 406 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 696
cert_cover_5 5 0 2 3 4 6 56 696 3
cert_coverFacet 6 920
cert_cover_5 6 0 2 3 6 7 664 920 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 224 992 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0523

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0524.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0524

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 405, 233, 433, 782, 838, 284, 452, 632, 792, 816, 992, 7, 11, 67, 21, 133, 41, 73, 49, 401, 161, 193, 14, 70, 774, 522, 578, 28, 268, 276, 196, 324, 388, 56, 280, 536, 104, 584, 776, 304, 560, 784, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_405, vertices_233, vertices_433, vertices_782, vertices_838, vertices_284, vertices_452, vertices_632, vertices_792, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_73, vertices_49, vertices_401, vertices_161, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_536, vertices_104, vertices_584, vertices_776, vertices_304, vertices_560, vertices_784, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_405), (false, vertices_233), (false, vertices_433), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 11 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 19 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_233) then 13 else
  if p.val = (false, vertices_433) then 17 else
  if p.val = (true, vertices_774) then 20 else
  if p.val = (true, vertices_268) then 0 else
  if p.val = (true, vertices_324) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 5 8 632 56 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 2 0 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 632
cert_cover_5 4 1 2 3 4 5 56 632 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 992
cert_cover_5 7 2 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0524

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0525.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0525

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 149, 809, 625, 209, 782, 838, 412, 452, 440, 240, 992, 7, 11, 67, 21, 133, 41, 521, 49, 81, 145, 545, 193, 577, 14, 70, 774, 522, 578, 28, 268, 148, 196, 324, 388, 56, 408, 296, 776, 112, 176, 208, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_809, vertices_625, vertices_209, vertices_782, vertices_838, vertices_412, vertices_452, vertices_440, vertices_240, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_81, vertices_145, vertices_545, vertices_193, vertices_577, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_196, vertices_324, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_112, vertices_176, vertices_208, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_809), (false, vertices_625), (false, vertices_209), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_408), (true, vertices_176), (true, vertices_224), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 13 10 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_625) then 11 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_774) then 19 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_408) then 12 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 3
  | 11 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
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
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 28 412 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 240
cert_cover_2 5 4 3 5 6 112 240 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0525

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0526.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0526

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 835, 589, 406, 282, 450, 556, 244, 612, 696, 920, 992, 7, 11, 67, 771, 13, 69, 521, 577, 22, 134, 26, 266, 274, 194, 322, 386, 44, 524, 52, 148, 100, 548, 196, 580, 56, 664, 280, 552, 776, 176, 400, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_835, vertices_589, vertices_406, vertices_282, vertices_450, vertices_556, vertices_244, vertices_612, vertices_696, vertices_920, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_13, vertices_69, vertices_521, vertices_577, vertices_22, vertices_134, vertices_26, vertices_266, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_524, vertices_52, vertices_148, vertices_100, vertices_548, vertices_196, vertices_580, vertices_56, vertices_664, vertices_280, vertices_552, vertices_776, vertices_176, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_835), (false, vertices_589), (true, vertices_274), (true, vertices_386), (true, vertices_148), (true, vertices_100), (true, vertices_548), (true, vertices_664), (true, vertices_280), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_835) then 20 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_664) then 22 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 8 664
cert_row_4 1 0 1 3 6 7 406 22 3
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 2 0 1 4
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 22 406 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 612
cert_cover_2 5 4 1 5 8 100 612 3
cert_coverFacet 6 696
cert_cover_5 6 0 2 3 4 6 56 696 3
cert_coverFacet 7 920
cert_cover_5 7 0 2 3 6 7 664 920 3
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 224 992 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0526

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0527.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0527

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 405, 617, 241, 782, 838, 284, 452, 696, 792, 912, 992, 7, 11, 67, 21, 133, 41, 585, 49, 145, 97, 193, 14, 70, 774, 522, 578, 28, 268, 276, 196, 324, 388, 56, 280, 536, 552, 776, 176, 400, 656, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_405, vertices_617, vertices_241, vertices_782, vertices_838, vertices_284, vertices_452, vertices_696, vertices_792, vertices_912, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_176, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_405), (false, vertices_617), (false, vertices_241), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_656), (true, vertices_784), (true, vertices_672), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 11 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 19 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_617) then 13 else
  if p.val = (false, vertices_241) then 17 else
  if p.val = (true, vertices_774) then 20 else
  if p.val = (true, vertices_268) then 0 else
  if p.val = (true, vertices_324) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 6 8 696 56 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 2 0 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coverFacet 7 992
cert_cover_5 7 2 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0527

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0528.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0528

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 405, 617, 241, 782, 838, 284, 452, 696, 408, 904, 992, 7, 11, 67, 21, 133, 41, 585, 49, 145, 97, 193, 14, 70, 774, 522, 578, 28, 268, 276, 196, 324, 388, 56, 152, 280, 552, 392, 648, 776, 176, 400, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_405, vertices_617, vertices_241, vertices_782, vertices_838, vertices_284, vertices_452, vertices_696, vertices_408, vertices_904, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_280, vertices_552, vertices_392, vertices_648, vertices_776, vertices_176, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_405), (false, vertices_617), (false, vertices_241), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_672), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 11 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 19 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_617) then 13 else
  if p.val = (false, vertices_241) then 17 else
  if p.val = (true, vertices_774) then 20 else
  if p.val = (true, vertices_268) then 0 else
  if p.val = (true, vertices_324) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 6 8 696 56 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 2 0 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 408
cert_cover_2 5 3 2 6 7 152 408 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 992
cert_cover_5 7 2 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0528

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0529.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0529

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 149, 169, 713, 433, 782, 838, 284, 468, 824, 680, 992, 7, 11, 67, 21, 133, 41, 585, 137, 49, 145, 161, 193, 14, 70, 774, 522, 578, 28, 268, 148, 276, 196, 324, 56, 280, 168, 552, 648, 776, 304, 400, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_169, vertices_713, vertices_433, vertices_782, vertices_838, vertices_284, vertices_468, vertices_824, vertices_680, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_137, vertices_49, vertices_145, vertices_161, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_276, vertices_196, vertices_324, vertices_56, vertices_280, vertices_168, vertices_552, vertices_648, vertices_776, vertices_304, vertices_400, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_169), (false, vertices_713), (false, vertices_433), (true, vertices_774), (true, vertices_268), (true, vertices_276), (true, vertices_324), (true, vertices_280), (true, vertices_552), (true, vertices_776), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 12 15 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 19 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_713) then 14 else
  if p.val = (false, vertices_433) then 17 else
  if p.val = (true, vertices_774) then 20 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 3 5 6 7 468 148 2
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 148 468 2
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0529

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0580.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0580

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 597, 121, 961, 398, 812, 564, 488, 880, 7, 11, 131, 259, 21, 517, 57, 73, 81, 193, 577, 385, 769, 14, 262, 138, 386, 44, 268, 52, 532, 548, 772, 104, 296, 200, 392, 112, 560, 592, 352, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_597, vertices_121, vertices_961, vertices_398, vertices_812, vertices_564, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_597), (false, vertices_121), (false, vertices_961), (true, vertices_268), (true, vertices_548), (true, vertices_296), (true, vertices_392), (true, vertices_560), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 13 16 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 12 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_800) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 812
cert_cover_5 1 1 1 2 4 7 44 812 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 488
cert_cover_5 3 2 2 4 5 6 104 488 3
cert_coverFacet 4 880
cert_cover_5 4 3 3 4 5 7 112 880 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0580

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0584.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0584

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 398, 156, 724, 632, 920, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 266, 386, 28, 140, 84, 148, 196, 56, 152, 536, 552, 392, 776, 112, 592, 656, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_398, vertices_156, vertices_724, vertices_632, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_28, vertices_140, vertices_84, vertices_148, vertices_196, vertices_56, vertices_152, vertices_536, vertices_552, vertices_392, vertices_776, vertices_112, vertices_592, vertices_656, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_140), (true, vertices_148), (true, vertices_152), (true, vertices_536), (true, vertices_392), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 10 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_737) then 18 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_656) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 2 3 6 7 8 920 152 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 156
cert_cover_2 1 2 1 3 6 28 156 3
cert_coverFacet 2 724
cert_cover_5 2 1 1 3 5 6 84 724 3
cert_coverFacet 3 632
cert_cover_5 3 2 2 3 4 5 56 632 3
cert_coverFacet 4 920
cert_cover_5 4 3 2 3 6 7 152 920 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0584

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0585.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0585

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 270, 906, 812, 308, 744, 880, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 266, 386, 44, 268, 52, 276, 292, 104, 552, 200, 648, 776, 112, 304, 336, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_270, vertices_906, vertices_812, vertices_308, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_304, vertices_336, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_266), (true, vertices_268), (true, vertices_292), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 14 17 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0585

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0586.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0586

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 721, 897, 270, 906, 812, 628, 744, 7, 11, 131, 21, 261, 57, 73, 81, 529, 193, 385, 641, 769, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 592, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_721, vertices_897, vertices_270, vertices_906, vertices_812, vertices_628, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_721), (false, vertices_897), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 13 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_789) then 12 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_608) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0586

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0587.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0587

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 593, 961, 270, 906, 812, 628, 744, 7, 11, 131, 21, 261, 57, 73, 81, 529, 193, 577, 385, 769, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 592, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_593, vertices_961, vertices_270, vertices_906, vertices_812, vertices_628, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_593), (false, vertices_961), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 13 16 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_789) then 12 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_608) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0587

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0598.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0598

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 597, 121, 961, 398, 300, 820, 488, 880, 7, 11, 131, 259, 21, 517, 57, 73, 81, 193, 577, 385, 769, 14, 262, 138, 386, 44, 268, 52, 532, 292, 772, 104, 296, 200, 392, 112, 816, 592, 352, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_597, vertices_121, vertices_961, vertices_398, vertices_300, vertices_820, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_816, vertices_592, vertices_352, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_597), (false, vertices_121), (false, vertices_961), (true, vertices_268), (true, vertices_292), (true, vertices_296), (true, vertices_392), (true, vertices_816), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 11 14 16 17 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 7 else
  if p.val = (false, vertices_203) then 8 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 10 else
  if p.val = (false, vertices_121) then 13 else
  if p.val = (false, vertices_961) then 18 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_816) then 15 else
  if p.val = (true, vertices_352) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_4 2 2 4 5 6 7 488 104 3
cert_rows_3
cert_pivot_3 0 3 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 300
cert_cover_2 1 2 1 4 7 44 300 3
cert_coverFacet 2 820
cert_cover_5 2 0 1 3 4 7 52 820 3
cert_coverFacet 3 488
cert_cover_5 3 2 2 4 5 6 104 488 3
cert_coverFacet 4 880
cert_cover_5 4 0 3 4 5 7 112 880 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 3 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0598

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0608.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0608

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 269, 905, 662, 122, 722, 812, 628, 900, 744, 7, 11, 131, 13, 261, 137, 265, 385, 22, 134, 58, 74, 82, 658, 194, 44, 268, 52, 532, 548, 388, 644, 772, 104, 552, 200, 648, 776, 112, 592, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_269, vertices_905, vertices_662, vertices_122, vertices_722, vertices_812, vertices_628, vertices_900, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_261, vertices_137, vertices_265, vertices_385, vertices_22, vertices_134, vertices_58, vertices_74, vertices_82, vertices_658, vertices_194, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_269), (false, vertices_905), (true, vertices_82), (true, vertices_658), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_592), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 12 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_905) then 19 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_658) then 17 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
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
cert_row_4 0 1 2 4 7 8 812 44 3
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_2 3 0 3 6 8 658
cert_row_2 4 0 2 3 4 58
cert_rows_2
cert_pivot 7 1 5 6 0
cert_heightProof 5
cert_coverFacet 0 662
cert_cover_5 0 3 0 1 3 6 22 662 3
cert_coverFacet 1 122
cert_cover_5 1 4 0 2 3 5 58 122 3
cert_coverFacet 2 722
cert_cover_5 2 3 0 3 5 6 82 722 3
cert_coverFacet 3 812
cert_cover_5 3 0 1 2 4 7 44 812 3
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 52 628 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 104 744 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0608

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0609.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0609

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 213, 121, 270, 906, 812, 564, 916, 744, 752, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 262, 138, 266, 386, 44, 268, 52, 148, 532, 548, 388, 772, 104, 552, 200, 648, 776, 112, 560, 208, 656, 736, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_213, vertices_121, vertices_270, vertices_906, vertices_812, vertices_564, vertices_916, vertices_744, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_148, vertices_532, vertices_548, vertices_388, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_736, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_213), (false, vertices_121), (true, vertices_266), (true, vertices_268), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_656), (true, vertices_736), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_736) then 21 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 6 8 736
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 916
cert_cover_5 4 3 1 3 6 7 148 916 3
cert_coverFacet 5 744
cert_cover_5 5 0 2 4 5 6 104 744 3
cert_coverFacet 6 752
cert_cover_5 6 0 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0609

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0617.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0617

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 721, 897, 782, 906, 556, 628, 744, 7, 11, 131, 21, 261, 57, 73, 81, 529, 193, 385, 641, 769, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 592, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_721, vertices_897, vertices_782, vertices_906, vertices_556, vertices_628, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_592, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_721), (false, vertices_897), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 6 16 9 17 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_391) then 7 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_789) then 8 else
  if p.val = (false, vertices_121) then 11 else
  if p.val = (false, vertices_721) then 12 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_778) then 15 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_608) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inl 1
  | 7 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 9 => Sum.inl 3
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0617

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0620.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0620

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 593, 961, 782, 906, 556, 628, 744, 7, 11, 131, 21, 261, 57, 73, 81, 529, 193, 577, 385, 769, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 592, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_593, vertices_961, vertices_782, vertices_906, vertices_556, vertices_628, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_592, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_593), (false, vertices_961), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 6 15 9 16 17 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_391) then 7 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_789) then 8 else
  if p.val = (false, vertices_121) then 11 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (false, vertices_961) then 18 else
  if p.val = (true, vertices_778) then 14 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_608) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inl 1
  | 7 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 9 => Sum.inl 3
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0620

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0621.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0621

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 533, 901, 121, 721, 270, 906, 812, 628, 744, 7, 11, 131, 21, 389, 517, 57, 73, 81, 529, 193, 641, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 592, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_533, vertices_901, vertices_121, vertices_721, vertices_270, vertices_906, vertices_812, vertices_628, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_389, vertices_517, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_641, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_533), (false, vertices_901), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 13 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 9 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_901) then 12 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_608) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0621

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0629.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0629

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 203, 899, 789, 121, 465, 526, 906, 812, 372, 488, 7, 11, 131, 515, 21, 517, 57, 73, 81, 273, 193, 385, 769, 14, 518, 138, 522, 898, 44, 524, 52, 276, 292, 772, 104, 296, 200, 392, 776, 112, 336, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_203, vertices_899, vertices_789, vertices_121, vertices_465, vertices_526, vertices_906, vertices_812, vertices_372, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_769, vertices_14, vertices_518, vertices_138, vertices_522, vertices_898, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_776, vertices_112, vertices_336, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_203), (false, vertices_899), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_522), (true, vertices_524), (true, vertices_292), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 13 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_203) then 9 else
  if p.val = (false, vertices_899) then 10 else
  if p.val = (false, vertices_789) then 12 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_352) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 6 7 8 898
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 372
cert_cover_5 3 2 1 3 4 5 52 372 3
cert_coverFacet 4 488
cert_cover_5 4 3 2 4 5 6 104 488 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0629

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0635.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0635

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 809, 737, 897, 334, 962, 348, 312, 880, 7, 11, 131, 53, 69, 41, 265, 97, 545, 193, 385, 641, 769, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 280, 296, 112, 304, 336, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_809, vertices_737, vertices_897, vertices_334, vertices_962, vertices_348, vertices_312, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_296, vertices_112, vertices_304, vertices_336, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_809), (false, vertices_737), (false, vertices_897), (true, vertices_322), (true, vertices_332), (true, vertices_280), (true, vertices_304), (true, vertices_336), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 13 15 16 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 7 else
  if p.val = (false, vertices_395) then 8 else
  if p.val = (false, vertices_117) then 11 else
  if p.val = (false, vertices_809) then 14 else
  if p.val = (false, vertices_737) then 17 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_332) then 12 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_304) then 3 else
  if p.val = (true, vertices_336) then 4 else
  if p.val = (true, vertices_832) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inl 4
  | 17 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 3 4 5 7 8 880 112 3
cert_rows_3
cert_pivot_3 0 1 3
cert_heightProof 3
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 28 348 3
cert_coverFacet 3 312
cert_cover_2 3 3 2 4 7 56 312 3
cert_coverFacet 4 880
cert_cover_5 4 2 3 4 5 7 112 880 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 3 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0635

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0652.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0652

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 533, 121, 457, 849, 654, 962, 556, 628, 744, 7, 11, 259, 21, 517, 57, 73, 393, 81, 529, 321, 769, 14, 518, 138, 386, 642, 770, 44, 524, 52, 532, 548, 104, 552, 200, 648, 112, 592, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_533, vertices_121, vertices_457, vertices_849, vertices_654, vertices_962, vertices_556, vertices_628, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_393, vertices_81, vertices_529, vertices_321, vertices_769, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_592, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_533), (false, vertices_121), (false, vertices_457), (false, vertices_849), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 15 11 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_121) then 13 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (false, vertices_849) then 14 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_704) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 386 1
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 386 962 1
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0652

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0653.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0653

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 398, 796, 468, 632, 976, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 266, 386, 28, 268, 84, 276, 196, 388, 56, 536, 552, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_398, vertices_796, vertices_468, vertices_632, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_28, vertices_268, vertices_84, vertices_276, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_268), (true, vertices_276), (true, vertices_388), (true, vertices_536), (true, vertices_464), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 13 15 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 8 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 9 else
  if p.val = (false, vertices_117) then 12 else
  if p.val = (false, vertices_809) then 14 else
  if p.val = (false, vertices_737) then 18 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_464) then 16 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_784) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 3 5 6 7 464
cert_row_4 2 1 2 3 7 8 796 28 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 796
cert_cover_5 1 2 1 2 3 7 28 796 3
cert_coverFacet 2 468
cert_cover_5 2 1 1 3 5 6 84 468 3
cert_coverFacet 3 632
cert_cover_5 3 3 2 3 4 5 56 632 3
cert_coverFacet 4 976
cert_cover_5 4 1 3 5 6 8 464 976 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0653

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0654.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0654

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 556, 628, 744, 976, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_556, vertices_628, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_592), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
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
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
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
cert_row_2 1 3 5 6 7 464
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 976
cert_cover_5 5 1 3 5 6 8 464 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0654

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0655.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0655

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 782, 906, 556, 820, 744, 880, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 816, 336, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_782, vertices_906, vertices_556, vertices_820, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_816, vertices_336, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_816), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 6 14 17 19 9 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 7 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_341) then 8 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_961) then 11 else
  if p.val = (true, vertices_778) then 13 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_608) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inl 1
  | 7 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 9 => Sum.inl 5
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_2 1 3 4 7 8 816
cert_row_4 2 2 4 5 6 8 744 104 3
cert_rows_3
cert_pivot_3 3 0 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 880
cert_cover_5 5 1 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0655

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0661.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0661

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 169, 737, 334, 962, 348, 696, 920, 880, 7, 11, 131, 53, 69, 41, 137, 97, 161, 193, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 664, 280, 168, 392, 112, 560, 336, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_169, vertices_737, vertices_334, vertices_962, vertices_348, vertices_696, vertices_920, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_664, vertices_280, vertices_168, vertices_392, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_169), (false, vertices_737), (true, vertices_322), (true, vertices_332), (true, vertices_664), (true, vertices_280), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 17 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_395) then 10 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_737) then 19 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_332) then 14 else
  if p.val = (true, vertices_664) then 16 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_336) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_832) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 7 332
cert_row_2 1 2 3 6 8 664
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 194 962 3
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 28 348 3
cert_coverFacet 3 696
cert_cover_5 3 1 2 3 4 6 56 696 3
cert_coverFacet 4 920
cert_cover_5 4 1 2 3 6 7 664 920 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0661

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0662.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0662

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 681, 737, 334, 962, 348, 568, 920, 880, 7, 11, 131, 53, 69, 41, 137, 97, 673, 193, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 280, 536, 552, 392, 648, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_681, vertices_737, vertices_334, vertices_962, vertices_348, vertices_568, vertices_920, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_673, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_536, vertices_552, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_681), (false, vertices_737), (true, vertices_322), (true, vertices_332), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 16 17 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_395) then 10 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_737) then 19 else
  if p.val = (true, vertices_322) then 0 else
  if p.val = (true, vertices_332) then 14 else
  if p.val = (true, vertices_280) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_336) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_832) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 6 7 8 920 280 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 28 348 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 920
cert_cover_5 4 2 2 3 6 7 280 920 2
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0662

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0664.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0664

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 653, 961, 342, 122, 458, 556, 820, 744, 880, 7, 11, 259, 13, 517, 137, 385, 641, 769, 22, 262, 58, 74, 394, 82, 322, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 816, 336, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_653, vertices_961, vertices_342, vertices_122, vertices_458, vertices_556, vertices_820, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_137, vertices_385, vertices_641, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_394, vertices_82, vertices_322, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_816, vertices_336, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_653), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_322), (true, vertices_276), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_112), (true, vertices_816), (true, vertices_336), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_816) then 19 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_608) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 2 4 5 6 8 744 104 3
cert_row_2 2 0 2 6 7 394
cert_row_2 3 3 4 7 8 816
cert_row_2 4 0 2 3 4 58
cert_rows_2
cert_pivot 1 5 6 7 0
cert_heightProof 5
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 122
cert_cover_5 1 4 0 2 3 5 58 122 3
cert_coverFacet 2 458
cert_cover_5 2 2 0 2 5 6 74 458 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 744
cert_cover_5 5 1 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0664

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0666.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0666

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 597, 121, 961, 398, 300, 820, 232, 936, 752, 7, 11, 131, 259, 21, 517, 57, 73, 81, 193, 577, 385, 769, 14, 262, 138, 386, 44, 268, 52, 532, 292, 772, 104, 168, 296, 200, 392, 112, 560, 592, 224, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_597, vertices_121, vertices_961, vertices_398, vertices_300, vertices_820, vertices_232, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_168, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_597), (false, vertices_121), (false, vertices_961), (true, vertices_268), (true, vertices_292), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 2 4 6 7 8 936 168 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 300
cert_cover_2 1 2 1 4 7 44 300 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 52 820 3
cert_coverFacet 3 232
cert_cover_2 3 4 2 5 6 104 232 3
cert_coverFacet 4 936
cert_cover_5 4 2 2 4 6 7 168 936 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0666

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0667.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0667

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 270, 906, 812, 628, 744, 720, 912, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 208, 592, 400, 656, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_270, vertices_906, vertices_812, vertices_628, vertices_744, vertices_720, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_592), (true, vertices_656), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
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
cert_coverFacet 5 720
cert_cover_2 5 5 3 6 8 208 720 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0667

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1050 : Certifies 1050 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0522.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1051 : Certifies 1051 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0523.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1052 : Certifies 1052 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0524.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1053 : Certifies 1053 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0525.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1054 : Certifies 1054 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0526.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1055 : Certifies 1055 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0527.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1056 : Certifies 1056 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0528.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1057 : Certifies 1057 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0529.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1058 : Certifies 1058 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0580.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1059 : Certifies 1059 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0584.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1060 : Certifies 1060 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0585.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1061 : Certifies 1061 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0586.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1062 : Certifies 1062 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0587.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1063 : Certifies 1063 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0598.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1064 : Certifies 1064 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0608.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1065 : Certifies 1065 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0609.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1066 : Certifies 1066 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0617.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1067 : Certifies 1067 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0620.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1068 : Certifies 1068 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0621.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1069 : Certifies 1069 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0629.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1070 : Certifies 1070 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0635.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1071 : Certifies 1071 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0652.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1072 : Certifies 1072 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0653.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1073 : Certifies 1073 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0654.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1074 : Certifies 1074 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0655.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1075 : Certifies 1075 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0661.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1076 : Certifies 1076 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0662.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1077 : Certifies 1077 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0664.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1078 : Certifies 1078 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0666.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1079 : Certifies 1079 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0667.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B035 (j : Fin 30) :
    Certifies (1050 + j.val) := by
  fin_cases j
  · exact projection_1050
  · exact projection_1051
  · exact projection_1052
  · exact projection_1053
  · exact projection_1054
  · exact projection_1055
  · exact projection_1056
  · exact projection_1057
  · exact projection_1058
  · exact projection_1059
  · exact projection_1060
  · exact projection_1061
  · exact projection_1062
  · exact projection_1063
  · exact projection_1064
  · exact projection_1065
  · exact projection_1066
  · exact projection_1067
  · exact projection_1068
  · exact projection_1069
  · exact projection_1070
  · exact projection_1071
  · exact projection_1072
  · exact projection_1073
  · exact projection_1074
  · exact projection_1075
  · exact projection_1076
  · exact projection_1077
  · exact projection_1078
  · exact projection_1079

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
