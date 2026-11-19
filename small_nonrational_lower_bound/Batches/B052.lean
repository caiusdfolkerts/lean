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
/- Source: ProjectionCertificates/R_multi_six_0215.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0215

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 267, 613, 809, 961, 222, 458, 564, 724, 440, 944, 7, 11, 259, 37, 69, 41, 265, 545, 321, 577, 769, 30, 70, 202, 266, 322, 52, 212, 532, 548, 580, 56, 152, 296, 392, 432, 560, 656, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_267, vertices_613, vertices_809, vertices_961, vertices_222, vertices_458, vertices_564, vertices_724, vertices_440, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_37, vertices_69, vertices_41, vertices_265, vertices_545, vertices_321, vertices_577, vertices_769, vertices_30, vertices_70, vertices_202, vertices_266, vertices_322, vertices_52, vertices_212, vertices_532, vertices_548, vertices_580, vertices_56, vertices_152, vertices_296, vertices_392, vertices_432, vertices_560, vertices_656, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_267), (false, vertices_613), (false, vertices_809), (false, vertices_961), (true, vertices_202), (true, vertices_212), (true, vertices_532), (true, vertices_152), (true, vertices_392), (true, vertices_432), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 13 15 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_327) then 7 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_613) then 11 else
  if p.val = (false, vertices_809) then 14 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_202) then 8 else
  if p.val = (true, vertices_212) then 12 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_392) then 3 else
  if p.val = (true, vertices_432) then 16 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_656) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 15 => Sum.inl 3
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
cert_row_4 1 0 1 2 5 3 222 30 3
cert_row_4 2 0 1 2 5 6 222 30 3
cert_rows_3
cert_pivot_3 3 4 0
cert_heightProof 3
cert_coverFacet 0 222
cert_cover_2 0 1 0 2 5 30 222 3
cert_coverFacet 1 458
cert_cover 1 5 1 0 2 3 0 7 2 202 458 202 30 222 5
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover 3 5 1 1 3 3 0 8 2 212 724 212 30 222 5
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 944
cert_cover_5 5 0 3 4 6 8 432 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0215

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_multi_six_0216.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0216

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 421, 809, 94, 198, 902, 706, 244, 440, 984, 7, 11, 515, 37, 261, 41, 521, 289, 769, 30, 70, 134, 774, 74, 194, 578, 642, 52, 84, 164, 196, 388, 56, 88, 408, 296, 584, 776, 176, 208, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_421, vertices_809, vertices_94, vertices_198, vertices_902, vertices_706, vertices_244, vertices_440, vertices_984] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_37, vertices_261, vertices_41, vertices_521, vertices_289, vertices_769, vertices_30, vertices_70, vertices_134, vertices_774, vertices_74, vertices_194, vertices_578, vertices_642, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_408, vertices_296, vertices_584, vertices_776, vertices_176, vertices_208, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_421), (false, vertices_809), (true, vertices_70), (true, vertices_134), (true, vertices_194), (true, vertices_642), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_408), (true, vertices_176), (true, vertices_208), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_408) then 19 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 6 244 52 3
cert_row_4 1 2 3 5 7 6 984 88 3
cert_row_4 2 2 3 5 7 8 984 88 3
cert_row_2 3 0 1 7 8 774
cert_row_2 4 0 1 2 3 30
cert_rows_2
cert_pivot 4 6 5 7 0
cert_heightProof 5
cert_coverFacet 0 94
cert_cover_5 0 4 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 902
cert_cover_5 2 3 0 1 6 7 134 902 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 52 244 3
cert_coverFacet 5 440
cert_cover 5 4 3 2 3 3 2 6 5 56 440 408 88 984 7
cert_coverFacet 6 984
cert_cover_2 6 3 2 5 7 88 984 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0216

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_multi_six_0217.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0217

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 903, 587, 421, 809, 94, 198, 706, 244, 440, 856, 976, 7, 11, 515, 37, 389, 41, 521, 289, 769, 30, 70, 134, 74, 194, 578, 642, 52, 84, 164, 196, 56, 88, 280, 296, 584, 776, 176, 208, 848, 400, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_903, vertices_587, vertices_421, vertices_809, vertices_94, vertices_198, vertices_706, vertices_244, vertices_440, vertices_856, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_37, vertices_389, vertices_41, vertices_521, vertices_289, vertices_769, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_578, vertices_642, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_208, vertices_848, vertices_400, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_903), (false, vertices_587), (false, vertices_421), (false, vertices_809), (true, vertices_70), (true, vertices_194), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_280), (true, vertices_176), (true, vertices_208), (true, vertices_848), (true, vertices_400), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_903) then 14 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_848) then 19 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_903), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_2 1 3 5 7 8 848
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 52 244 3
cert_coverFacet 4 440
cert_cover_5 4 3 2 3 4 6 56 440 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0217

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_multi_six_0218.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0218

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 977, 782, 646, 458, 898, 812, 376, 7, 27, 67, 37, 133, 49, 81, 785, 545, 193, 641, 14, 134, 518, 74, 266, 194, 386, 642, 770, 44, 780, 548, 644, 56, 88, 296, 328, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_977, vertices_782, vertices_646, vertices_458, vertices_898, vertices_812, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_785, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_518, vertices_74, vertices_266, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_977), (true, vertices_518), (true, vertices_266), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_780), (true, vertices_296), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 14 15 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 8 else
  if p.val = (false, vertices_91) then 9 else
  if p.val = (false, vertices_677) then 12 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (false, vertices_977) then 19 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_780) then 13 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_977), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 44 812 3
cert_coverFacet 5 376
cert_cover_5 5 2 2 3 4 5 56 376 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0218

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_multi_six_0219.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0219

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 907, 93, 457, 678, 554, 372, 484, 568, 856, 944, 7, 11, 131, 29, 69, 73, 393, 193, 38, 134, 42, 522, 546, 642, 52, 84, 356, 164, 196, 56, 88, 536, 552, 328, 776, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_907, vertices_93, vertices_457, vertices_678, vertices_554, vertices_372, vertices_484, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_393, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_907), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_356), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 16 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_907) then 17 else
  if p.val = (false, vertices_93) then 14 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_356) then 15 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_907), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 4 5 7 356
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 372
cert_cover_5 2 1 1 3 4 5 52 372 3
cert_coverFacet 3 484
cert_cover_5 3 1 1 4 5 6 356 484 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0219

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_multi_six_0220.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0220

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 651, 707, 221, 806, 554, 834, 372, 440, 936, 976, 7, 11, 67, 643, 29, 69, 137, 193, 38, 262, 42, 522, 546, 322, 578, 770, 52, 84, 292, 324, 56, 152, 424, 552, 648, 304, 208, 336, 400, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_651, vertices_707, vertices_221, vertices_806, vertices_554, vertices_834, vertices_372, vertices_440, vertices_936, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_643, vertices_29, vertices_69, vertices_137, vertices_193, vertices_38, vertices_262, vertices_42, vertices_522, vertices_546, vertices_322, vertices_578, vertices_770, vertices_52, vertices_84, vertices_292, vertices_324, vertices_56, vertices_152, vertices_424, vertices_552, vertices_648, vertices_304, vertices_208, vertices_336, vertices_400, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_651), (false, vertices_707), (false, vertices_221), (true, vertices_546), (true, vertices_770), (true, vertices_292), (true, vertices_424), (true, vertices_552), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 10 16 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 11 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_221) then 17 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_424) then 18 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_221), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 7 424
cert_row_4 1 0 1 4 7 8 806 38 3
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 38 806 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 372
cert_cover_5 3 2 1 3 4 5 52 372 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 936
cert_cover_5 5 0 2 4 6 8 424 936 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0220

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_multi_six_0221.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0221

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 651, 899, 221, 449, 294, 810, 628, 868, 696, 976, 7, 11, 643, 259, 29, 69, 137, 193, 321, 385, 38, 262, 42, 522, 290, 770, 52, 84, 612, 292, 324, 56, 152, 552, 648, 560, 208, 592, 656, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_651, vertices_899, vertices_221, vertices_449, vertices_294, vertices_810, vertices_628, vertices_868, vertices_696, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_643, vertices_259, vertices_29, vertices_69, vertices_137, vertices_193, vertices_321, vertices_385, vertices_38, vertices_262, vertices_42, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_612, vertices_292, vertices_324, vertices_56, vertices_152, vertices_552, vertices_648, vertices_560, vertices_208, vertices_592, vertices_656, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_651), (false, vertices_899), (false, vertices_221), (false, vertices_449), (true, vertices_290), (true, vertices_612), (true, vertices_292), (true, vertices_552), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 9 10 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_221) then 12 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inl 3
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_221), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 294
cert_cover_2 0 1 0 4 7 38 294 3
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 42 810 3
cert_coverFacet 2 628
cert_cover_5 2 0 1 3 4 5 52 628 3
cert_coverFacet 3 868
cert_cover_5 3 0 1 4 5 7 612 868 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0221

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_multi_six_0224.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0224

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 977, 142, 458, 812, 908, 376, 7, 27, 67, 37, 133, 49, 81, 785, 545, 193, 641, 14, 134, 74, 138, 194, 44, 140, 780, 548, 644, 56, 88, 296, 328, 392, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_977, vertices_142, vertices_458, vertices_812, vertices_908, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_785, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_780, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_977), (true, vertices_138), (true, vertices_140), (true, vertices_780), (true, vertices_296), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 5 8 12 13 15 16 18 19 20
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 9 else
  if p.val = (false, vertices_199) then 6 else
  if p.val = (false, vertices_91) then 7 else
  if p.val = (false, vertices_677) then 10 else
  if p.val = (false, vertices_817) then 14 else
  if p.val = (false, vertices_977) then 17 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_780) then 11 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_392) then 4 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inl 0
  | 6 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 15 => Sum.inl 4
  | 16 => Sum.inl 5
  | 17 => Sum.inr ⟨(false, vertices_977), by decide +kernel⟩
  | 18 => Sum.inl 6
  | 19 => Sum.inl 7
  | 20 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0224

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_multi_six_0225.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0225

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 451, 933, 369, 206, 684, 824, 728, 976, 7, 27, 67, 131, 37, 133, 49, 81, 289, 321, 385, 14, 134, 74, 194, 44, 140, 676, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_451, vertices_933, vertices_369, vertices_206, vertices_684, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_289, vertices_321, vertices_385, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_676, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_451), (false, vertices_933), (false, vertices_369), (true, vertices_140), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_720), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 12 13 16 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 8 else
  if p.val = (false, vertices_451) then 9 else
  if p.val = (false, vertices_933) then 17 else
  if p.val = (false, vertices_369) then 14 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_720) then 15 else
  if p.val = (true, vertices_784) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inr ⟨(false, vertices_933), by decide +kernel⟩
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 3 5 6 8 720
cert_row_2 2 1 4 6 8 676
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0225

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_multi_six_0227.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0227

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 977, 654, 458, 812, 376, 904, 7, 27, 67, 37, 133, 49, 81, 785, 545, 193, 641, 14, 134, 74, 138, 194, 44, 524, 548, 644, 56, 88, 296, 328, 392, 648, 776, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_977, vertices_654, vertices_458, vertices_812, vertices_376, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_785, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_977), (true, vertices_138), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 13 14 16 17 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 8 else
  if p.val = (false, vertices_91) then 9 else
  if p.val = (false, vertices_677) then 12 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (false, vertices_977) then 18 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_296) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inr ⟨(false, vertices_977), by decide +kernel⟩
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0227

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_new_prism_0080.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0080

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 555, 309, 453, 737, 353, 158, 202, 842, 706, 404, 824, 472, 864, 7, 43, 515, 53, 133, 261, 97, 289, 545, 193, 321, 641, 30, 134, 74, 138, 522, 194, 578, 642, 148, 276, 388, 56, 152, 280, 552, 200, 328, 776, 304, 400, 352, 608, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_555, vertices_309, vertices_453, vertices_737, vertices_353, vertices_158, vertices_202, vertices_842, vertices_706, vertices_404, vertices_824, vertices_472, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_43, vertices_515, vertices_53, vertices_133, vertices_261, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_30, vertices_134, vertices_74, vertices_138, vertices_522, vertices_194, vertices_578, vertices_642, vertices_148, vertices_276, vertices_388, vertices_56, vertices_152, vertices_280, vertices_552, vertices_200, vertices_328, vertices_776, vertices_304, vertices_400, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_555), (false, vertices_309), (false, vertices_453), (false, vertices_737), (false, vertices_353), (true, vertices_74), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_148), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_328), (true, vertices_776), (true, vertices_400), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 1 0 4 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 6 30 158 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 152 472 2
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0080

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_new_prism_0118.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0118

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 647, 147, 781, 293, 817, 721, 126, 526, 218, 906, 364, 456, 624, 992, 7, 19, 131, 37, 261, 517, 49, 145, 529, 289, 641, 769, 14, 54, 518, 90, 138, 522, 146, 642, 108, 268, 524, 292, 200, 328, 392, 776, 112, 560, 208, 592, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_647, vertices_147, vertices_781, vertices_293, vertices_817, vertices_721, vertices_126, vertices_526, vertices_218, vertices_906, vertices_364, vertices_456, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_131, vertices_37, vertices_261, vertices_517, vertices_49, vertices_145, vertices_529, vertices_289, vertices_641, vertices_769, vertices_14, vertices_54, vertices_518, vertices_90, vertices_138, vertices_522, vertices_146, vertices_642, vertices_108, vertices_268, vertices_524, vertices_292, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_647), (false, vertices_147), (false, vertices_781), (false, vertices_293), (false, vertices_817), (false, vertices_721), (true, vertices_14), (true, vertices_90), (true, vertices_138), (true, vertices_522), (true, vertices_108), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_112), (true, vertices_352), (true, vertices_608), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 14 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 3 126 14 3
cert_row_4 1 0 1 2 4 5 126 14 3
cert_row_4 2 0 2 6 7 8 906 138 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 3 1 0 4
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 4 14 126 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 218
cert_cover 2 3 1 0 2 3 0 6 2 90 218 90 14 126 4
cert_coverFacet 3 906
cert_cover_5 3 2 0 2 6 7 138 906 3
cert_coverFacet 4 364
cert_cover 4 4 1 1 2 3 0 7 2 108 364 108 14 126 4
cert_coverFacet 5 456
cert_cover_2 5 5 2 6 7 200 456 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 352 992 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0118

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_new_prism_0397.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0397

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 391, 651, 781, 721, 865, 449, 126, 310, 602, 402, 658, 620, 804, 496, 7, 11, 131, 13, 261, 521, 193, 321, 577, 385, 641, 769, 14, 54, 262, 90, 522, 146, 274, 530, 386, 642, 108, 524, 292, 548, 772, 584, 112, 304, 208, 592, 400, 656, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_391, vertices_651, vertices_781, vertices_721, vertices_865, vertices_449, vertices_126, vertices_310, vertices_602, vertices_402, vertices_658, vertices_620, vertices_804, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_261, vertices_521, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_54, vertices_262, vertices_90, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_108, vertices_524, vertices_292, vertices_548, vertices_772, vertices_584, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_391), (false, vertices_651), (false, vertices_781), (false, vertices_721), (false, vertices_865), (false, vertices_449), (true, vertices_54), (true, vertices_90), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_108), (true, vertices_292), (true, vertices_548), (true, vertices_584), (true, vertices_112), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 11 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_721) then 12 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_54) then 13 else
  if p.val = (true, vertices_90) then 14 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_108) then 20 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 3 4 5 6 7 496 112 3
cert_row_4 1 0 1 2 3 4 126 14 3
cert_row_4 2 0 1 2 3 5 126 14 3
cert_rows_3
cert_pivot_3 4 6 0
cert_heightProof 3
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 14 126 3
cert_coverFacet 1 310
cert_cover 1 3 1 0 1 3 0 7 2 54 310 54 14 126 3
cert_coverFacet 2 602
cert_cover 2 3 1 0 2 3 0 8 2 90 602 90 14 126 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 620
cert_cover 5 4 1 1 2 3 0 8 2 108 620 108 14 126 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 496
cert_cover_5 7 0 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0397

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_new_prism_0502.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0502

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 539, 109, 201, 905, 817, 481, 526, 118, 198, 902, 466, 786, 716, 368, 27, 45, 73, 137, 521, 49, 529, 97, 289, 193, 385, 769, 14, 54, 70, 134, 518, 522, 82, 274, 530, 194, 386, 770, 76, 524, 100, 196, 644, 200, 648, 112, 304, 336, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_539, vertices_109, vertices_201, vertices_905, vertices_817, vertices_481, vertices_526, vertices_118, vertices_198, vertices_902, vertices_466, vertices_786, vertices_716, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_521, vertices_49, vertices_529, vertices_97, vertices_289, vertices_193, vertices_385, vertices_769, vertices_14, vertices_54, vertices_70, vertices_134, vertices_518, vertices_522, vertices_82, vertices_274, vertices_530, vertices_194, vertices_386, vertices_770, vertices_76, vertices_524, vertices_100, vertices_196, vertices_644, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_539), (false, vertices_109), (false, vertices_201), (false, vertices_905), (false, vertices_817), (false, vertices_481), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_82), (true, vertices_274), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_524), (true, vertices_196), (true, vertices_644), (true, vertices_112), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_539) then 15 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 3 5 6 7 466 82 3
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 118
cert_cover_5 1 0 0 1 3 5 54 118 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 902
cert_cover_5 3 2 0 1 6 7 134 902 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 82 466 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 76 716 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0502

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_new_prism_0677.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0677

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 539, 109, 201, 905, 817, 481, 526, 118, 454, 646, 338, 914, 716, 368, 27, 45, 73, 137, 521, 49, 529, 97, 289, 193, 385, 769, 14, 54, 70, 134, 518, 522, 82, 274, 530, 322, 386, 642, 76, 524, 100, 196, 644, 200, 648, 112, 304, 336, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_539, vertices_109, vertices_201, vertices_905, vertices_817, vertices_481, vertices_526, vertices_118, vertices_454, vertices_646, vertices_338, vertices_914, vertices_716, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_521, vertices_49, vertices_529, vertices_97, vertices_289, vertices_193, vertices_385, vertices_769, vertices_14, vertices_54, vertices_70, vertices_134, vertices_518, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_386, vertices_642, vertices_76, vertices_524, vertices_100, vertices_196, vertices_644, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_539), (false, vertices_109), (false, vertices_201), (false, vertices_905), (false, vertices_817), (false, vertices_481), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_82), (true, vertices_274), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_524), (true, vertices_196), (true, vertices_644), (true, vertices_112), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_539) then 15 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 0 3 6 7 8 914 274 2
cert_row_4 2 0 1 5 6 7 454 70 3
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 118
cert_cover_5 1 0 0 1 3 5 54 118 3
cert_coverFacet 2 454
cert_cover_5 2 2 0 1 5 6 70 454 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 914
cert_cover_5 5 1 0 3 6 7 274 914 2
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 76 716 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0677

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_new_prism_0706.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0706

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 555, 181, 453, 929, 158, 198, 326, 202, 842, 632, 216, 496, 864, 7, 43, 515, 53, 133, 261, 161, 545, 385, 769, 30, 70, 134, 262, 74, 138, 522, 194, 322, 770, 148, 196, 324, 56, 88, 152, 552, 200, 584, 112, 176, 208, 352, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_555, vertices_181, vertices_453, vertices_929, vertices_158, vertices_198, vertices_326, vertices_202, vertices_842, vertices_632, vertices_216, vertices_496, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_43, vertices_515, vertices_53, vertices_133, vertices_261, vertices_161, vertices_545, vertices_385, vertices_769, vertices_30, vertices_70, vertices_134, vertices_262, vertices_74, vertices_138, vertices_522, vertices_194, vertices_322, vertices_770, vertices_148, vertices_196, vertices_324, vertices_56, vertices_88, vertices_152, vertices_552, vertices_200, vertices_584, vertices_112, vertices_176, vertices_208, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_555), (false, vertices_181), (false, vertices_453), (false, vertices_929), (true, vertices_70), (true, vertices_134), (true, vertices_74), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_112), (true, vertices_208), (true, vertices_352), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 6 30 158 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 842
cert_cover_5 4 1 0 2 5 7 74 842 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0706

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_new_prism_0711.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0711

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 555, 181, 453, 929, 158, 198, 326, 202, 842, 632, 216, 688, 976, 7, 43, 515, 53, 133, 261, 161, 545, 385, 769, 30, 70, 134, 262, 74, 138, 522, 194, 322, 770, 148, 196, 324, 56, 88, 152, 552, 200, 584, 176, 560, 208, 592, 656, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_555, vertices_181, vertices_453, vertices_929, vertices_158, vertices_198, vertices_326, vertices_202, vertices_842, vertices_632, vertices_216, vertices_688, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_43, vertices_515, vertices_53, vertices_133, vertices_261, vertices_161, vertices_545, vertices_385, vertices_769, vertices_30, vertices_70, vertices_134, vertices_262, vertices_74, vertices_138, vertices_522, vertices_194, vertices_322, vertices_770, vertices_148, vertices_196, vertices_324, vertices_56, vertices_88, vertices_152, vertices_552, vertices_200, vertices_584, vertices_176, vertices_560, vertices_208, vertices_592, vertices_656, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_555), (false, vertices_181), (false, vertices_453), (false, vertices_929), (true, vertices_70), (true, vertices_134), (true, vertices_74), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 6 30 158 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 842
cert_cover_5 4 1 0 2 5 7 74 842 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coverFacet 8 976
cert_cover_5 8 3 3 5 6 7 208 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0711

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_new_prism_0741.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0741

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 555, 181, 453, 929, 158, 198, 326, 202, 842, 824, 216, 344, 496, 7, 43, 515, 53, 133, 261, 161, 545, 385, 769, 30, 70, 134, 262, 74, 138, 522, 194, 322, 770, 148, 196, 324, 56, 88, 152, 280, 552, 200, 328, 776, 176, 304, 208, 336, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_555, vertices_181, vertices_453, vertices_929, vertices_158, vertices_198, vertices_326, vertices_202, vertices_842, vertices_824, vertices_216, vertices_344, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_43, vertices_515, vertices_53, vertices_133, vertices_261, vertices_161, vertices_545, vertices_385, vertices_769, vertices_30, vertices_70, vertices_134, vertices_262, vertices_74, vertices_138, vertices_522, vertices_194, vertices_322, vertices_770, vertices_148, vertices_196, vertices_324, vertices_56, vertices_88, vertices_152, vertices_280, vertices_552, vertices_200, vertices_328, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_555), (false, vertices_181), (false, vertices_453), (false, vertices_929), (true, vertices_70), (true, vertices_134), (true, vertices_74), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_200), (true, vertices_328), (true, vertices_776), (true, vertices_304), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 6 30 158 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 842
cert_cover_5 4 1 0 2 5 7 74 842 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0741

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1353.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1353

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 181, 901, 681, 94, 586, 962, 340, 404, 632, 496, 736, 7, 11, 259, 53, 133, 261, 41, 521, 161, 641, 769, 30, 70, 74, 522, 322, 578, 770, 84, 148, 276, 324, 388, 56, 88, 552, 584, 112, 176, 336, 400, 224, 608, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_181, vertices_901, vertices_681, vertices_94, vertices_586, vertices_962, vertices_340, vertices_404, vertices_632, vertices_496, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_133, vertices_261, vertices_41, vertices_521, vertices_161, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_522, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_276, vertices_324, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_181), (false, vertices_901), (false, vertices_681), (true, vertices_74), (true, vertices_578), (true, vertices_84), (true, vertices_276), (true, vertices_88), (true, vertices_584), (true, vertices_112), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 5 6 7 8 962 322 2
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 322 962 2
cert_coverFacet 3 340
cert_cover_2 3 3 1 5 7 84 340 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1353

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1354.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1354

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 369, 961, 654, 458, 706, 188, 676, 344, 408, 944, 7, 27, 67, 37, 517, 49, 81, 289, 321, 577, 769, 14, 518, 74, 138, 194, 578, 642, 60, 140, 164, 548, 644, 88, 152, 280, 328, 392, 176, 304, 336, 400, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_369, vertices_961, vertices_654, vertices_458, vertices_706, vertices_188, vertices_676, vertices_344, vertices_408, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_138, vertices_194, vertices_578, vertices_642, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_280, vertices_328, vertices_392, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_369), (false, vertices_961), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_583) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_672) then 12 else
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
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 5 0 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 188
cert_cover_5 3 2 1 2 3 6 60 188 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1354

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1355.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1355

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 181, 617, 929, 94, 838, 586, 340, 404, 248, 976, 736, 7, 11, 259, 53, 133, 41, 521, 161, 545, 385, 769, 30, 70, 262, 74, 522, 578, 770, 84, 148, 276, 324, 388, 56, 88, 104, 584, 176, 208, 336, 400, 224, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_181, vertices_617, vertices_929, vertices_94, vertices_838, vertices_586, vertices_340, vertices_404, vertices_248, vertices_976, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_133, vertices_41, vertices_521, vertices_161, vertices_545, vertices_385, vertices_769, vertices_30, vertices_70, vertices_262, vertices_74, vertices_522, vertices_578, vertices_770, vertices_84, vertices_148, vertices_276, vertices_324, vertices_388, vertices_56, vertices_88, vertices_104, vertices_584, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_181), (false, vertices_617), (false, vertices_929), (true, vertices_70), (true, vertices_74), (true, vertices_578), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_88), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 4 2 0 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 838
cert_cover_5 1 2 0 1 5 7 70 838 3
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 340
cert_cover_2 3 3 1 5 7 84 340 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 248
cert_cover_5 5 0 2 3 4 5 56 248 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1355

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1356.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1356

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 421, 645, 369, 961, 654, 842, 188, 344, 664, 792, 944, 7, 27, 67, 37, 133, 517, 49, 81, 289, 321, 577, 385, 641, 14, 518, 74, 522, 578, 60, 140, 164, 644, 88, 152, 280, 536, 328, 648, 776, 176, 304, 336, 656, 784, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_421, vertices_645, vertices_369, vertices_961, vertices_654, vertices_842, vertices_188, vertices_344, vertices_664, vertices_792, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_518, vertices_74, vertices_522, vertices_578, vertices_60, vertices_140, vertices_164, vertices_644, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_648, vertices_776, vertices_176, vertices_304, vertices_336, vertices_656, vertices_784, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_421), (false, vertices_645), (false, vertices_369), (false, vertices_961), (true, vertices_522), (true, vertices_140), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_648), (true, vertices_776), (true, vertices_176), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_583) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_645) then 0 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 5 0 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 188
cert_cover_5 2 2 1 2 3 6 60 188 3
cert_coverFacet 3 344
cert_cover_2 3 3 2 5 7 88 344 3
cert_coverFacet 4 664
cert_cover_2 4 3 2 6 8 152 664 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1356

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1357.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1357

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 233, 961, 94, 838, 340, 660, 788, 376, 944, 480, 7, 11, 515, 53, 133, 41, 73, 161, 193, 577, 641, 30, 70, 518, 74, 578, 84, 148, 276, 532, 324, 644, 772, 56, 88, 104, 176, 304, 336, 656, 784, 224, 352, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_233, vertices_961, vertices_94, vertices_838, vertices_340, vertices_660, vertices_788, vertices_376, vertices_944, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_193, vertices_577, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_176, vertices_304, vertices_336, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_233), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_304), (true, vertices_336), (true, vertices_656), (true, vertices_784), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 3 4 6 7 8 944 176 3
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_2 2 0 1 2 3 30
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 8 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 5 30 94 3
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 340
cert_cover_2 2 3 1 5 7 84 340 3
cert_coverFacet 3 660
cert_cover_2 3 3 1 6 8 148 660 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 7 176 944 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1357

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1358.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1358

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 329, 905, 689, 849, 142, 86, 838, 390, 458, 628, 932, 27, 45, 73, 137, 265, 49, 81, 529, 161, 321, 641, 769, 14, 22, 70, 134, 262, 74, 138, 82, 322, 386, 140, 52, 84, 164, 548, 580, 388, 772, 328, 392, 560, 592, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_329, vertices_905, vertices_689, vertices_849, vertices_142, vertices_86, vertices_838, vertices_390, vertices_458, vertices_628, vertices_932] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_265, vertices_49, vertices_81, vertices_529, vertices_161, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_134, vertices_262, vertices_74, vertices_138, vertices_82, vertices_322, vertices_386, vertices_140, vertices_52, vertices_84, vertices_164, vertices_548, vertices_580, vertices_388, vertices_772, vertices_328, vertices_392, vertices_560, vertices_592, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_329), (false, vertices_905), (false, vertices_689), (false, vertices_849), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_138), (true, vertices_322), (true, vertices_386), (true, vertices_84), (true, vertices_548), (true, vertices_580), (true, vertices_388), (true, vertices_772)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_905) then 18 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_772) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 70 838 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 458
cert_cover_5 4 0 0 2 5 6 74 458 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 52 628 3
cert_coverFacet 6 932
cert_cover_5 6 3 1 4 6 7 164 932 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1358

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1359.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1359

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 428, 652, 120, 872, 904, 496, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 140, 524, 164, 644, 56, 88, 104, 296, 584, 392, 648, 776, 112, 176, 336, 400, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_428, vertices_652, vertices_120, vertices_872, vertices_904, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_140, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_296, vertices_584, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_140), (true, vertices_524), (true, vertices_104), (true, vertices_296), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_112), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
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
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 337 1 140 524 104 296 584 392 648 776 112 352 416 647 181 63 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 428
cert_cover_5 1 1 1 2 4 6 44 428 3
cert_coverFacet 2 652
cert_cover_2 2 2 1 6 8 140 652 3
cert_coverFacet 3 120
cert_cover_2 3 3 2 4 5 56 120 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1359

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1360.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1360

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 428, 780, 900, 120, 872, 496, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 268, 524, 164, 388, 644, 772, 56, 88, 104, 296, 584, 776, 112, 176, 336, 400, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_428, vertices_780, vertices_900, vertices_120, vertices_872, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_268, vertices_524, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_296, vertices_584, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_268), (true, vertices_524), (true, vertices_388), (true, vertices_772), (true, vertices_104), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_112), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
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
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 337 1 268 524 388 772 104 296 584 776 112 352 416 647 181 63 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 428
cert_cover_5 1 1 1 2 4 6 44 428 3
cert_coverFacet 2 780
cert_cover_2 2 2 1 7 8 268 780 3
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 120
cert_cover_2 4 3 2 4 5 56 120 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1360

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1361.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1361

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 172, 908, 120, 872, 424, 496, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 140, 524, 164, 644, 56, 88, 104, 168, 296, 584, 392, 776, 112, 176, 336, 400, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_172, vertices_908, vertices_120, vertices_872, vertices_424, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_140, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_168, vertices_296, vertices_584, vertices_392, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_140), (true, vertices_524), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_584), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
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
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 337 1 140 524 104 168 296 584 392 776 112 352 416 647 181 63 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 6 7 8 908 140 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 172
cert_cover_2 1 2 1 4 6 44 172 3
cert_coverFacet 2 908
cert_cover_5 2 1 1 2 6 7 140 908 3
cert_coverFacet 3 120
cert_cover_2 3 3 2 4 5 56 120 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1361

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1362.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1362

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 300, 908, 420, 120, 872, 496, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 268, 524, 164, 292, 388, 644, 56, 88, 104, 296, 584, 776, 112, 176, 336, 400, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_300, vertices_908, vertices_420, vertices_120, vertices_872, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_268, vertices_524, vertices_164, vertices_292, vertices_388, vertices_644, vertices_56, vertices_88, vertices_104, vertices_296, vertices_584, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_388), (true, vertices_104), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_112), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
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
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 337 1 268 524 292 388 104 296 584 776 112 352 416 647 181 63 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 6 7 8 908 268 2
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 300
cert_cover_2 1 2 1 4 7 44 300 3
cert_coverFacet 2 908
cert_cover_5 2 1 1 2 6 7 268 908 2
cert_coverFacet 3 420
cert_cover_2 3 4 1 6 7 164 420 3
cert_coverFacet 4 120
cert_cover_2 4 3 2 4 5 56 120 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1362

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1363.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1363

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 556, 932, 248, 872, 464, 480, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 524, 164, 548, 644, 56, 88, 104, 552, 584, 176, 208, 336, 400, 224, 352, 416, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_556, vertices_932, vertices_248, vertices_872, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_524), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_208), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
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
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 337 1 524 548 104 552 584 208 224 352 416 800 448 647 181 63 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 4 6 7 8 932 164 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 556
cert_cover_2 1 2 1 4 8 44 556 3
cert_coverFacet 2 932
cert_cover_5 2 1 1 4 6 7 164 932 3
cert_coverFacet 3 248
cert_cover_5 3 2 2 3 4 5 56 248 3
cert_coverFacet 4 872
cert_cover_5 4 3 2 4 5 7 104 872 3
cert_coverFacet 5 464
cert_cover_2 5 5 3 6 7 208 464 3
cert_coverFacet 6 480
cert_cover_2 6 5 4 6 7 224 480 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1363

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1364.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1364

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 556, 932, 184, 472, 872, 424, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 524, 164, 548, 644, 56, 88, 152, 168, 296, 552, 328, 584, 392, 176, 336, 400, 416, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_556, vertices_932, vertices_184, vertices_472, vertices_872, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_152, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_176, vertices_336, vertices_400, vertices_416, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_524), (true, vertices_548), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
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
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 337 1 524 548 152 168 296 552 328 584 392 416 800 647 181 63 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 4 6 7 8 932 164 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 556
cert_cover_2 1 2 1 4 8 44 556 3
cert_coverFacet 2 932
cert_cover_5 2 1 1 4 6 7 164 932 3
cert_coverFacet 3 184
cert_cover_2 3 3 2 4 6 56 184 3
cert_coverFacet 4 472
cert_cover_5 4 2 2 3 5 6 88 472 3
cert_coverFacet 5 872
cert_cover_5 5 3 2 4 5 7 296 872 2
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1364

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1560 : Certifies 1560 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0215.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1561 : Certifies 1561 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0216.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1562 : Certifies 1562 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0217.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1563 : Certifies 1563 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0218.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1564 : Certifies 1564 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0219.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1565 : Certifies 1565 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0220.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1566 : Certifies 1566 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0221.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1567 : Certifies 1567 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0224.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1568 : Certifies 1568 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0225.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1569 : Certifies 1569 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0227.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1570 : Certifies 1570 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0080.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1571 : Certifies 1571 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0118.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1572 : Certifies 1572 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0397.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1573 : Certifies 1573 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0502.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1574 : Certifies 1574 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0677.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1575 : Certifies 1575 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0706.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1576 : Certifies 1576 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0711.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1577 : Certifies 1577 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_new_prism_0741.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1578 : Certifies 1578 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1353.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1579 : Certifies 1579 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1354.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1580 : Certifies 1580 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1355.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1581 : Certifies 1581 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1356.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1582 : Certifies 1582 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1357.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1583 : Certifies 1583 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1358.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1584 : Certifies 1584 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1359.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1585 : Certifies 1585 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1360.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1586 : Certifies 1586 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1361.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1587 : Certifies 1587 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1362.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1588 : Certifies 1588 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1363.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1589 : Certifies 1589 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1364.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B052 (j : Fin 30) :
    Certifies (1560 + j.val) := by
  fin_cases j
  · exact projection_1560
  · exact projection_1561
  · exact projection_1562
  · exact projection_1563
  · exact projection_1564
  · exact projection_1565
  · exact projection_1566
  · exact projection_1567
  · exact projection_1568
  · exact projection_1569
  · exact projection_1570
  · exact projection_1571
  · exact projection_1572
  · exact projection_1573
  · exact projection_1574
  · exact projection_1575
  · exact projection_1576
  · exact projection_1577
  · exact projection_1578
  · exact projection_1579
  · exact projection_1580
  · exact projection_1581
  · exact projection_1582
  · exact projection_1583
  · exact projection_1584
  · exact projection_1585
  · exact projection_1586
  · exact projection_1587
  · exact projection_1588
  · exact projection_1589

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
