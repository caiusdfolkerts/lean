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
/- Source: ProjectionCertificates/R_one_six_0976.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0976

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 341, 121, 457, 654, 962, 684, 820, 232, 752, 848, 7, 11, 259, 21, 261, 57, 73, 393, 81, 321, 14, 518, 138, 386, 642, 770, 44, 652, 52, 276, 548, 772, 104, 168, 200, 112, 560, 336, 592, 784, 224, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_341, vertices_121, vertices_457, vertices_654, vertices_962, vertices_684, vertices_820, vertices_232, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_393, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 18 15 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_395) then 19 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_652) then 14 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0976

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0977.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0977

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 267, 789, 809, 625, 78, 198, 202, 906, 124, 468, 744, 976, 7, 11, 259, 21, 261, 41, 265, 49, 529, 545, 769, 14, 70, 134, 74, 138, 266, 194, 386, 60, 76, 84, 276, 196, 388, 104, 552, 200, 648, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_267, vertices_789, vertices_809, vertices_625, vertices_78, vertices_198, vertices_202, vertices_906, vertices_124, vertices_468, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_769, vertices_14, vertices_70, vertices_134, vertices_74, vertices_138, vertices_266, vertices_194, vertices_386, vertices_60, vertices_76, vertices_84, vertices_276, vertices_196, vertices_388, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_267), (false, vertices_789), (false, vertices_809), (false, vertices_625), (true, vertices_70), (true, vertices_74), (true, vertices_138), (true, vertices_194), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_200), (true, vertices_648), (true, vertices_464), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_464) then 22 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_2 1 3 5 6 7 464
cert_row_4 2 0 2 6 7 8 906 138 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 906
cert_cover_5 3 2 0 2 6 7 138 906 3
cert_coverFacet 4 124
cert_cover_5 4 0 1 2 3 5 60 124 3
cert_coverFacet 5 468
cert_cover_5 5 1 1 3 5 6 84 468 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 976
cert_cover_5 7 1 3 5 6 8 464 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0977

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0978.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0978

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 117, 617, 961, 398, 198, 284, 212, 916, 824, 752, 7, 11, 67, 259, 53, 69, 41, 521, 97, 449, 577, 769, 14, 70, 134, 266, 194, 386, 28, 268, 84, 148, 276, 196, 388, 56, 280, 552, 776, 112, 560, 208, 656, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_117, vertices_617, vertices_961, vertices_398, vertices_198, vertices_284, vertices_212, vertices_916, vertices_824, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_449, vertices_577, vertices_769, vertices_14, vertices_70, vertices_134, vertices_266, vertices_194, vertices_386, vertices_28, vertices_268, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_617), (false, vertices_961), (true, vertices_134), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_280), (true, vertices_560), (true, vertices_208), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 20 21 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_451) then 22 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
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
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 148 916 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0978

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0979.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0979

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 75, 195, 899, 789, 121, 465, 526, 714, 684, 372, 932, 488, 7, 11, 67, 131, 515, 21, 517, 57, 73, 81, 273, 193, 385, 769, 14, 518, 74, 522, 194, 642, 44, 524, 52, 276, 676, 292, 772, 104, 168, 200, 648, 112, 336, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_75, vertices_195, vertices_899, vertices_789, vertices_121, vertices_465, vertices_526, vertices_714, vertices_684, vertices_372, vertices_932, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_515, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_522, vertices_194, vertices_642, vertices_44, vertices_524, vertices_52, vertices_276, vertices_676, vertices_292, vertices_772, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_336, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_75), (false, vertices_195), (false, vertices_899), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_522), (true, vertices_524), (true, vertices_676), (true, vertices_292), (true, vertices_168), (true, vertices_200), (true, vertices_648), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_195) then 2 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_676) then 15 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
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
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_2 1 1 4 6 8 676
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 372
cert_cover_5 3 2 1 3 4 5 52 372 3
cert_coverFacet 4 932
cert_cover_5 4 1 1 4 6 7 676 932 3
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0979

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0980.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0980

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 661, 361, 817, 78, 198, 902, 458, 124, 212, 752, 992, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 70, 134, 518, 74, 266, 194, 386, 770, 60, 76, 84, 148, 196, 644, 104, 328, 112, 560, 208, 656, 736, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_78, vertices_198, vertices_902, vertices_458, vertices_124, vertices_212, vertices_752, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_70, vertices_134, vertices_518, vertices_74, vertices_266, vertices_194, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_560, vertices_208, vertices_656, vertices_736, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_70), (true, vertices_134), (true, vertices_74), (true, vertices_194), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_736), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_736) then 23 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_2 1 4 5 6 8 736
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 0 2 5 6 7 458 74 3
cert_rows
cert_pivot_2 3 4 1 0
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 134 902 3
cert_coverFacet 3 458
cert_cover_5 3 3 0 2 5 6 74 458 3
cert_coverFacet 4 124
cert_cover_5 4 0 1 2 3 5 60 124 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 6 112 752 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 736 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0980

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0981.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0981

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 117, 361, 526, 198, 902, 540, 724, 696, 936, 496, 7, 11, 67, 259, 53, 69, 41, 265, 97, 321, 14, 70, 134, 518, 522, 194, 386, 770, 28, 524, 84, 532, 196, 644, 56, 536, 680, 296, 776, 112, 176, 208, 656, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_198, vertices_902, vertices_540, vertices_724, vertices_696, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_70, vertices_134, vertices_518, vertices_522, vertices_194, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_680, vertices_296, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_134), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_536), (true, vertices_680), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_680) then 21 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 8 680
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 902
cert_cover_5 2 1 0 1 6 7 134 902 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 696
cert_cover_5 5 0 2 3 4 6 56 696 3
cert_coverFacet 6 936
cert_cover_5 6 0 2 4 6 7 680 936 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0981

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0982.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0982

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 75, 661, 121, 849, 961, 654, 458, 556, 820, 360, 936, 368, 7, 11, 67, 21, 133, 57, 73, 81, 529, 193, 833, 641, 14, 134, 74, 138, 194, 44, 524, 52, 532, 548, 644, 104, 296, 552, 328, 392, 648, 112, 304, 336, 784, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_75, vertices_661, vertices_121, vertices_849, vertices_961, vertices_654, vertices_458, vertices_556, vertices_820, vertices_360, vertices_936, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_833, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_644, vertices_104, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_784, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_75), (false, vertices_661), (false, vertices_121), (false, vertices_849), (false, vertices_961), (true, vertices_138), (true, vertices_524), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_392), (true, vertices_648), (true, vertices_304), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 16 19 20 21 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_661) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 936
cert_cover_5 5 3 2 4 6 7 296 936 2
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0982

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0983.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0983

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 75, 789, 901, 121, 465, 654, 458, 556, 564, 360, 936, 880, 7, 11, 67, 21, 133, 773, 57, 73, 81, 273, 193, 385, 14, 134, 74, 138, 194, 44, 524, 52, 532, 548, 644, 104, 296, 552, 328, 392, 648, 112, 560, 336, 784, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_75, vertices_789, vertices_901, vertices_121, vertices_465, vertices_654, vertices_458, vertices_556, vertices_564, vertices_360, vertices_936, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_773, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_644, vertices_104, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_75), (false, vertices_789), (false, vertices_901), (false, vertices_121), (false, vertices_465), (true, vertices_138), (true, vertices_524), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_392), (true, vertices_648), (true, vertices_560), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 2 4 6 7 8 936 296 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 936
cert_cover_5 5 2 2 4 6 7 296 936 2
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0983

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0984.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0984

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 75, 661, 121, 465, 782, 902, 458, 556, 564, 872, 368, 944, 7, 11, 67, 21, 133, 57, 73, 81, 145, 193, 14, 134, 774, 74, 266, 194, 386, 44, 524, 52, 532, 548, 644, 104, 552, 328, 776, 112, 304, 560, 336, 400, 656, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_75, vertices_661, vertices_121, vertices_465, vertices_782, vertices_902, vertices_458, vertices_556, vertices_564, vertices_872, vertices_368, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_14, vertices_134, vertices_774, vertices_74, vertices_266, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_644, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_400, vertices_656, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_75), (false, vertices_661), (false, vertices_121), (false, vertices_465), (true, vertices_774), (true, vertices_266), (true, vertices_386), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_352), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 22 13 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 20 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_465) then 18 else
  if p.val = (true, vertices_774) then 21 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 2 5 6 7 458 74 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0984

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0985.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0985

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 75, 661, 121, 465, 654, 842, 962, 812, 564, 360, 368, 944, 7, 11, 67, 21, 133, 57, 73, 81, 145, 193, 14, 134, 74, 522, 194, 834, 642, 44, 524, 52, 532, 548, 644, 104, 296, 328, 776, 112, 304, 560, 336, 400, 656, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_75, vertices_661, vertices_121, vertices_465, vertices_654, vertices_842, vertices_962, vertices_812, vertices_564, vertices_360, vertices_368, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_14, vertices_134, vertices_74, vertices_522, vertices_194, vertices_834, vertices_642, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_644, vertices_104, vertices_296, vertices_328, vertices_776, vertices_112, vertices_304, vertices_560, vertices_336, vertices_400, vertices_656, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_75), (false, vertices_661), (false, vertices_121), (false, vertices_465), (true, vertices_522), (true, vertices_834), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_296), (true, vertices_328), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_352), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_834) then 15 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_37 75 522 642 524 548 296 328 776 304 560 352 800 896 199 834 661 63 121 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 5 0 1 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 360
cert_cover_2 5 4 2 5 7 104 360 3
cert_coverFacet 6 368
cert_cover_2 6 4 3 5 7 112 368 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0985

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0986.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0986

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 75, 451, 213, 901, 121, 526, 842, 556, 692, 360, 936, 496, 7, 11, 67, 259, 21, 133, 773, 57, 73, 81, 193, 385, 14, 518, 74, 522, 322, 770, 44, 524, 52, 148, 548, 644, 104, 296, 552, 328, 776, 112, 176, 208, 352, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_75, vertices_451, vertices_213, vertices_901, vertices_121, vertices_526, vertices_842, vertices_556, vertices_692, vertices_360, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_133, vertices_773, vertices_57, vertices_73, vertices_81, vertices_193, vertices_385, vertices_14, vertices_518, vertices_74, vertices_522, vertices_322, vertices_770, vertices_44, vertices_524, vertices_52, vertices_148, vertices_548, vertices_644, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_112, vertices_176, vertices_208, vertices_352, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_75), (false, vertices_451), (false, vertices_213), (false, vertices_901), (false, vertices_121), (true, vertices_522), (true, vertices_524), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_176), (true, vertices_352), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 17 14 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 18 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 2 4 6 7 8 936 296 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 936
cert_cover_5 5 2 2 4 6 7 296 936 2
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0986

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0989.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0989

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 139, 451, 341, 121, 201, 526, 906, 684, 820, 232, 752, 976, 7, 11, 131, 259, 21, 261, 57, 73, 137, 81, 193, 321, 14, 518, 138, 522, 386, 770, 44, 524, 52, 276, 548, 772, 104, 168, 200, 648, 112, 560, 720, 336, 784, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_139, vertices_451, vertices_341, vertices_121, vertices_201, vertices_526, vertices_906, vertices_684, vertices_820, vertices_232, vertices_752, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_321, vertices_14, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_560, vertices_720, vertices_336, vertices_784, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_139), (false, vertices_451), (false, vertices_341), (false, vertices_121), (false, vertices_201), (true, vertices_522), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_720), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_720) then 21 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 752
cert_cover_5 5 0 3 4 5 6 112 752 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0989

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0990.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0990

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 139, 451, 341, 121, 201, 526, 906, 556, 692, 916, 744, 496, 7, 11, 131, 259, 21, 261, 57, 73, 137, 81, 193, 321, 14, 518, 138, 522, 386, 770, 44, 524, 52, 660, 276, 548, 772, 104, 552, 200, 648, 112, 176, 336, 400, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_139, vertices_451, vertices_341, vertices_121, vertices_201, vertices_526, vertices_906, vertices_556, vertices_692, vertices_916, vertices_744, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_321, vertices_14, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_660, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_139), (false, vertices_451), (false, vertices_341), (false, vertices_121), (false, vertices_201), (true, vertices_522), (true, vertices_524), (true, vertices_660), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 15 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_660) then 20 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 6 8 660
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 692
cert_cover_5 3 0 1 3 4 6 52 692 3
cert_coverFacet 4 916
cert_cover_5 4 0 1 3 6 7 660 916 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0990

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0997.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0997

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 117, 197, 425, 225, 590, 198, 962, 604, 824, 752, 928, 7, 11, 259, 53, 69, 133, 41, 265, 97, 161, 193, 385, 14, 70, 134, 522, 194, 578, 386, 770, 28, 588, 84, 196, 56, 536, 296, 776, 112, 560, 592, 224, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_117, vertices_197, vertices_425, vertices_225, vertices_590, vertices_198, vertices_962, vertices_604, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_69, vertices_133, vertices_41, vertices_265, vertices_97, vertices_161, vertices_193, vertices_385, vertices_14, vertices_70, vertices_134, vertices_522, vertices_194, vertices_578, vertices_386, vertices_770, vertices_28, vertices_588, vertices_84, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_560, vertices_592, vertices_224, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_117), (false, vertices_197), (false, vertices_425), (false, vertices_225), (true, vertices_70), (true, vertices_194), (true, vertices_578), (true, vertices_588), (true, vertices_536), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_588) then 18 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 5 28 604 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0997

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0998.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0998

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 117, 197, 425, 225, 590, 198, 962, 604, 184, 920, 752, 7, 11, 259, 53, 69, 133, 41, 265, 97, 161, 193, 385, 14, 70, 134, 522, 194, 578, 386, 770, 28, 588, 84, 196, 56, 152, 536, 168, 392, 776, 112, 176, 592, 656, 224, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_117, vertices_197, vertices_425, vertices_225, vertices_590, vertices_198, vertices_962, vertices_604, vertices_184, vertices_920, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_69, vertices_133, vertices_41, vertices_265, vertices_97, vertices_161, vertices_193, vertices_385, vertices_14, vertices_70, vertices_134, vertices_522, vertices_194, vertices_578, vertices_386, vertices_770, vertices_28, vertices_588, vertices_84, vertices_196, vertices_56, vertices_152, vertices_536, vertices_168, vertices_392, vertices_776, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_117), (false, vertices_197), (false, vertices_425), (false, vertices_225), (true, vertices_70), (true, vertices_194), (true, vertices_578), (true, vertices_588), (true, vertices_152), (true, vertices_536), (true, vertices_176), (true, vertices_592), (true, vertices_656), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_588) then 18 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 6 7 8 920 152 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 5 28 604 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 920
cert_cover_5 5 2 2 3 6 7 152 920 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0998

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0999.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0999

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 779, 597, 425, 817, 398, 198, 962, 124, 204, 232, 496, 848, 7, 11, 515, 21, 581, 41, 265, 49, 529, 289, 769, 14, 70, 134, 266, 194, 578, 386, 770, 60, 76, 140, 84, 196, 104, 168, 200, 392, 112, 304, 336, 592, 784, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_779, vertices_597, vertices_425, vertices_817, vertices_398, vertices_198, vertices_962, vertices_124, vertices_204, vertices_232, vertices_496, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_581, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_70, vertices_134, vertices_266, vertices_194, vertices_578, vertices_386, vertices_770, vertices_60, vertices_76, vertices_140, vertices_84, vertices_196, vertices_104, vertices_168, vertices_200, vertices_392, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_779), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_336), (true, vertices_224), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_583) then 17 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
cert_nodeAtPriority_11 134 194 386 76 140 196 104 200 112 336 224 448 832 779 63 583 597 425 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0999

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 597, 121, 201, 270, 838, 962, 300, 820, 232, 936, 752, 7, 11, 131, 21, 69, 57, 73, 137, 81, 193, 14, 70, 262, 266, 194, 834, 386, 44, 268, 52, 532, 292, 580, 772, 104, 168, 296, 200, 392, 112, 560, 592, 224, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_597, vertices_121, vertices_201, vertices_270, vertices_838, vertices_962, vertices_300, vertices_820, vertices_232, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_194, vertices_834, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_104, vertices_168, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_597), (false, vertices_121), (false, vertices_201), (true, vertices_262), (true, vertices_834), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_296), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 20 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_834) then 18 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 2 4 6 7 8 936 168 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 52 820 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 936
cert_cover_5 6 2 2 4 6 7 168 936 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1004

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 707, 597, 297, 817, 398, 898, 124, 204, 488, 752, 928, 7, 11, 195, 515, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 134, 266, 386, 642, 770, 60, 76, 140, 84, 196, 104, 296, 200, 392, 112, 560, 592, 224, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_707, vertices_597, vertices_297, vertices_817, vertices_398, vertices_898, vertices_124, vertices_204, vertices_488, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_515, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_140, vertices_84, vertices_196, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_707), (false, vertices_597), (false, vertices_297), (false, vertices_817), (true, vertices_386), (true, vertices_76), (true, vertices_140), (true, vertices_104), (true, vertices_200), (true, vertices_392), (true, vertices_112), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 14 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 204
cert_cover_2 3 2 1 5 6 76 204 3
cert_coverFacet 4 488
cert_cover_5 4 2 2 4 5 6 104 488 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1005

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 707, 597, 297, 817, 398, 898, 124, 204, 488, 368, 976, 7, 11, 195, 515, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 134, 266, 386, 642, 770, 60, 76, 140, 84, 196, 104, 296, 200, 392, 112, 304, 336, 592, 784, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_707, vertices_597, vertices_297, vertices_817, vertices_398, vertices_898, vertices_124, vertices_204, vertices_488, vertices_368, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_515, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_140, vertices_84, vertices_196, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_707), (false, vertices_597), (false, vertices_297), (false, vertices_817), (true, vertices_386), (true, vertices_76), (true, vertices_140), (true, vertices_104), (true, vertices_200), (true, vertices_392), (true, vertices_112), (true, vertices_336), (true, vertices_352), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 14 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 204
cert_cover_2 3 2 1 5 6 76 204 3
cert_coverFacet 4 488
cert_cover_5 4 2 2 4 5 6 104 488 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 336 976 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1006

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 86, 198, 122, 202, 300, 820, 724, 488, 880, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 70, 134, 58, 74, 138, 82, 194, 44, 268, 52, 84, 532, 292, 196, 644, 772, 104, 296, 200, 392, 112, 816, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_86, vertices_198, vertices_122, vertices_202, vertices_300, vertices_820, vertices_724, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_70, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_268, vertices_52, vertices_84, vertices_532, vertices_292, vertices_196, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_816, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_70), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_84), (true, vertices_532), (true, vertices_292), (true, vertices_196), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_816), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_816) then 22 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_46 70 74 82 194 84 532 292 196 104 296 200 112 592 352 647 395 781 816
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_2 2 3 4 7 8 816
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 122
cert_cover_5 2 0 0 2 3 5 58 122 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 820
cert_cover_5 5 2 1 3 4 7 52 820 3
cert_coverFacet 6 724
cert_cover_5 6 1 1 3 5 6 84 724 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coverFacet 8 880
cert_cover_5 8 2 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1009

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 117, 197, 809, 481, 654, 962, 92, 204, 568, 728, 880, 7, 11, 259, 53, 69, 133, 41, 777, 97, 289, 193, 385, 14, 134, 522, 386, 642, 770, 28, 76, 140, 84, 196, 56, 88, 536, 552, 200, 648, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_117, vertices_197, vertices_809, vertices_481, vertices_654, vertices_962, vertices_92, vertices_204, vertices_568, vertices_728, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_69, vertices_133, vertices_41, vertices_777, vertices_97, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_140, vertices_84, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_117), (false, vertices_197), (false, vertices_809), (false, vertices_481), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_88), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 204
cert_cover_2 3 2 1 5 6 76 204 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 88 728 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1010

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 150, 122, 202, 210, 300, 820, 724, 488, 880, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 134, 58, 74, 138, 82, 146, 194, 44, 268, 52, 148, 532, 292, 644, 772, 104, 296, 200, 392, 112, 816, 208, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_150, vertices_122, vertices_202, vertices_210, vertices_300, vertices_820, vertices_724, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_146, vertices_194, vertices_44, vertices_268, vertices_52, vertices_148, vertices_532, vertices_292, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_816, vertices_208, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_148), (true, vertices_532), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_816), (true, vertices_208), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_816) then 22 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_46 74 82 146 194 148 532 292 104 296 200 112 208 592 352 647 395 781 816
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 1 3 5 6 8 724 148 2
cert_row_2 2 3 4 7 8 816
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 820
cert_cover_5 5 2 1 3 4 7 52 820 3
cert_coverFacet 6 724
cert_cover_5 6 1 1 3 5 6 148 724 2
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coverFacet 8 880
cert_cover_5 8 2 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1011

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 117, 197, 809, 481, 654, 962, 156, 212, 568, 728, 880, 7, 11, 259, 53, 69, 133, 41, 777, 97, 289, 193, 385, 14, 134, 522, 386, 642, 770, 28, 140, 84, 148, 196, 56, 152, 536, 552, 648, 112, 560, 208, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_117, vertices_197, vertices_809, vertices_481, vertices_654, vertices_962, vertices_156, vertices_212, vertices_568, vertices_728, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_69, vertices_133, vertices_41, vertices_777, vertices_97, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_84, vertices_148, vertices_196, vertices_56, vertices_152, vertices_536, vertices_552, vertices_648, vertices_112, vertices_560, vertices_208, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_117), (false, vertices_197), (false, vertices_809), (false, vertices_481), (true, vertices_642), (true, vertices_140), (true, vertices_148), (true, vertices_152), (true, vertices_536), (true, vertices_648), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 2 3 5 6 8 728 152 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 152 728 2
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1012

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 214, 122, 202, 300, 820, 660, 488, 880, 720, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 134, 58, 74, 138, 82, 194, 44, 268, 52, 148, 532, 292, 644, 772, 104, 296, 200, 392, 112, 816, 208, 592, 656, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_214, vertices_122, vertices_202, vertices_300, vertices_820, vertices_660, vertices_488, vertices_880, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_268, vertices_52, vertices_148, vertices_532, vertices_292, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_816, vertices_208, vertices_592, vertices_656, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_148), (true, vertices_532), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_816), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_816) then 22 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_46 74 82 194 148 532 292 104 296 200 112 208 592 656 352 647 395 781 816
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 3 5 6 214 22 3
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 660
cert_cover_2 5 3 1 6 8 148 660 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 880
cert_cover_5 7 0 3 4 5 7 112 880 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1013

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1014.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1014

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 213, 121, 201, 782, 962, 812, 692, 360, 456, 880, 720, 7, 11, 131, 21, 133, 57, 73, 137, 81, 193, 14, 518, 266, 386, 642, 770, 44, 780, 52, 148, 548, 644, 104, 296, 200, 328, 392, 112, 560, 208, 592, 656, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_213, vertices_121, vertices_201, vertices_782, vertices_962, vertices_812, vertices_692, vertices_360, vertices_456, vertices_880, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_52, vertices_148, vertices_548, vertices_644, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_213), (false, vertices_121), (false, vertices_201), (true, vertices_770), (true, vertices_780), (true, vertices_548), (true, vertices_296), (true, vertices_328), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_352), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 20 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_780) then 18 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 456
cert_cover_2 5 5 2 6 7 200 456 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1014

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1015.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 213, 121, 201, 782, 962, 812, 564, 660, 488, 880, 720, 7, 11, 131, 21, 133, 57, 73, 137, 81, 193, 14, 518, 266, 386, 642, 770, 44, 780, 52, 148, 532, 548, 644, 104, 296, 200, 392, 112, 560, 208, 592, 656, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_213, vertices_121, vertices_201, vertices_782, vertices_962, vertices_812, vertices_564, vertices_660, vertices_488, vertices_880, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_52, vertices_148, vertices_532, vertices_548, vertices_644, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_213), (false, vertices_121), (false, vertices_201), (true, vertices_770), (true, vertices_780), (true, vertices_532), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_352), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 20 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_780) then 18 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 488
cert_cover_5 5 2 2 4 5 6 104 488 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1015

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1016.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 214, 122, 202, 300, 820, 596, 708, 488, 880, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 134, 58, 74, 138, 82, 194, 44, 268, 52, 84, 532, 292, 196, 580, 644, 772, 104, 296, 200, 392, 112, 816, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_214, vertices_122, vertices_202, vertices_300, vertices_820, vertices_596, vertices_708, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_268, vertices_52, vertices_84, vertices_532, vertices_292, vertices_196, vertices_580, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_816, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_84), (true, vertices_532), (true, vertices_292), (true, vertices_196), (true, vertices_580), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_816), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_816) then 22 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_46 74 82 194 84 532 292 196 580 104 296 200 112 592 352 647 395 781 816
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 3 5 6 214 22 3
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coverFacet 8 880
cert_cover_5 8 0 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1016

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1017.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 213, 121, 201, 782, 962, 812, 564, 596, 708, 488, 880, 7, 11, 131, 21, 133, 57, 73, 137, 81, 193, 14, 518, 266, 386, 642, 770, 44, 780, 52, 84, 532, 548, 196, 580, 644, 104, 296, 200, 392, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_213, vertices_121, vertices_201, vertices_782, vertices_962, vertices_812, vertices_564, vertices_596, vertices_708, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_213), (false, vertices_121), (false, vertices_201), (true, vertices_770), (true, vertices_780), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_352), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 20 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_780) then 18 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_coverFacet 4 596
cert_cover_2 4 3 1 5 8 84 596 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 488
cert_cover_5 6 2 2 4 5 6 104 488 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1017

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1018.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 214, 122, 202, 300, 820, 724, 488, 368, 848, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 134, 58, 74, 138, 82, 194, 44, 268, 52, 212, 532, 292, 644, 772, 104, 296, 200, 392, 112, 304, 336, 592, 784, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_214, vertices_122, vertices_202, vertices_300, vertices_820, vertices_724, vertices_488, vertices_368, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_268, vertices_52, vertices_212, vertices_532, vertices_292, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_212), (true, vertices_532), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_212) then 20 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_2 2 1 3 5 6 212
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 22 214 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 52 820 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 8 212 724 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1018

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1019.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 214, 122, 202, 300, 820, 724, 488, 624, 864, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 134, 58, 74, 138, 82, 194, 44, 268, 52, 212, 532, 292, 644, 772, 104, 296, 200, 392, 112, 560, 592, 352, 608, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_214, vertices_122, vertices_202, vertices_300, vertices_820, vertices_724, vertices_488, vertices_624, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_268, vertices_52, vertices_212, vertices_532, vertices_292, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_212), (true, vertices_532), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_352), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_212) then 20 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_2 2 1 3 5 6 212
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 22 214 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 52 820 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 8 212 724 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1019

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1290 : Certifies 1290 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0976.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1291 : Certifies 1291 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0977.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1292 : Certifies 1292 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0978.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1293 : Certifies 1293 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0979.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1294 : Certifies 1294 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0980.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1295 : Certifies 1295 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0981.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1296 : Certifies 1296 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0982.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1297 : Certifies 1297 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0983.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1298 : Certifies 1298 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0984.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1299 : Certifies 1299 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0985.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1300 : Certifies 1300 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0986.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1301 : Certifies 1301 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0989.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1302 : Certifies 1302 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0990.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1303 : Certifies 1303 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0997.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1304 : Certifies 1304 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0998.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1305 : Certifies 1305 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0999.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1306 : Certifies 1306 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1307 : Certifies 1307 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1308 : Certifies 1308 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1309 : Certifies 1309 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1310 : Certifies 1310 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1311 : Certifies 1311 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1312 : Certifies 1312 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1313 : Certifies 1313 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1314 : Certifies 1314 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1014.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1315 : Certifies 1315 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1015.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1316 : Certifies 1316 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1016.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1317 : Certifies 1317 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1017.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1318 : Certifies 1318 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1018.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1319 : Certifies 1319 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1019.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B043 (j : Fin 30) :
    Certifies (1290 + j.val) := by
  fin_cases j
  · exact projection_1290
  · exact projection_1291
  · exact projection_1292
  · exact projection_1293
  · exact projection_1294
  · exact projection_1295
  · exact projection_1296
  · exact projection_1297
  · exact projection_1298
  · exact projection_1299
  · exact projection_1300
  · exact projection_1301
  · exact projection_1302
  · exact projection_1303
  · exact projection_1304
  · exact projection_1305
  · exact projection_1306
  · exact projection_1307
  · exact projection_1308
  · exact projection_1309
  · exact projection_1310
  · exact projection_1311
  · exact projection_1312
  · exact projection_1313
  · exact projection_1314
  · exact projection_1315
  · exact projection_1316
  · exact projection_1317
  · exact projection_1318
  · exact projection_1319

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
