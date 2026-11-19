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
/- Source: ProjectionCertificates/R_multi_six_0172.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0172

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 625, 961, 398, 330, 450, 444, 856, 944, 7, 27, 67, 37, 133, 49, 81, 545, 193, 577, 641, 14, 134, 74, 266, 194, 322, 386, 60, 396, 164, 88, 280, 328, 432, 560, 592, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_625, vertices_961, vertices_398, vertices_330, vertices_450, vertices_444, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_134, vertices_74, vertices_266, vertices_194, vertices_322, vertices_386, vertices_60, vertices_396, vertices_164, vertices_88, vertices_280, vertices_328, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_625), (false, vertices_961), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_396), (true, vertices_280), (true, vertices_328), (true, vertices_432), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 13 14 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 7 else
  if p.val = (false, vertices_91) then 8 else
  if p.val = (false, vertices_677) then 11 else
  if p.val = (false, vertices_625) then 15 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_396) then 12 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_432) then 16 else
  if p.val = (true, vertices_784) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
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
cert_row_4 0 1 2 3 6 4 444 60 3
cert_row_4 1 1 2 3 6 7 444 60 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_rows_3
cert_pivot_3 1 4 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover 0 2 2 0 1 3 1 6 3 14 398 396 60 444 6
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 444
cert_cover_2 3 2 1 3 6 60 444 3
cert_coverFacet 4 856
cert_cover_5 4 2 2 3 5 7 88 856 3
cert_coverFacet 5 944
cert_cover 5 6 2 3 4 3 1 8 3 432 944 432 60 444 6
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0172

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_multi_six_0173.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0173

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 625, 705, 398, 330, 962, 444, 856, 944, 7, 27, 67, 37, 133, 49, 81, 545, 193, 577, 641, 14, 134, 74, 266, 194, 322, 386, 60, 396, 164, 88, 280, 328, 432, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_625, vertices_705, vertices_398, vertices_330, vertices_962, vertices_444, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_134, vertices_74, vertices_266, vertices_194, vertices_322, vertices_386, vertices_60, vertices_396, vertices_164, vertices_88, vertices_280, vertices_328, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_625), (false, vertices_705), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_396), (true, vertices_280), (true, vertices_328), (true, vertices_432), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_677) then 14 else
  if p.val = (false, vertices_625) then 18 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_432) then 19 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_832) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 2 3 6 4 444 60 3
cert_row_4 2 1 2 3 6 7 444 60 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover 0 2 2 0 1 3 1 6 3 14 398 396 60 444 6
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 444
cert_cover_2 3 2 1 3 6 60 444 3
cert_coverFacet 4 856
cert_cover_5 4 3 2 3 5 7 88 856 3
cert_coverFacet 5 944
cert_cover 5 6 2 3 4 3 1 8 3 432 944 432 60 444 6
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0173

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_multi_six_0174.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0174

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 677, 625, 398, 646, 330, 962, 444, 856, 944, 7, 27, 67, 37, 517, 49, 81, 545, 577, 14, 134, 518, 74, 266, 322, 578, 386, 642, 60, 396, 164, 644, 88, 280, 328, 432, 560, 592, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_677, vertices_625, vertices_398, vertices_646, vertices_330, vertices_962, vertices_444, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_134, vertices_518, vertices_74, vertices_266, vertices_322, vertices_578, vertices_386, vertices_642, vertices_60, vertices_396, vertices_164, vertices_644, vertices_88, vertices_280, vertices_328, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_677), (false, vertices_625), (true, vertices_134), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_396), (true, vertices_280), (true, vertices_328), (true, vertices_432), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_583) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_396) then 16 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_432) then 20 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 322 2
cert_row_4 1 1 2 3 6 4 444 60 3
cert_row_4 2 1 2 3 6 7 444 60 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover 0 2 2 0 1 3 1 6 3 14 398 396 60 444 6
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 7 322 962 2
cert_coverFacet 4 444
cert_cover_2 4 2 1 3 6 60 444 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 944
cert_cover 6 6 2 3 4 3 1 8 3 432 944 432 60 444 6
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0174

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_multi_six_0175.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0175

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 903, 587, 181, 681, 94, 326, 834, 468, 376, 872, 944, 7, 11, 515, 53, 133, 41, 521, 161, 641, 30, 70, 262, 74, 322, 578, 770, 84, 148, 324, 388, 56, 88, 360, 552, 584, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_903, vertices_587, vertices_181, vertices_681, vertices_94, vertices_326, vertices_834, vertices_468, vertices_376, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_521, vertices_161, vertices_641, vertices_30, vertices_70, vertices_262, vertices_74, vertices_322, vertices_578, vertices_770, vertices_84, vertices_148, vertices_324, vertices_388, vertices_56, vertices_88, vertices_360, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_903), (false, vertices_587), (false, vertices_181), (false, vertices_681), (true, vertices_70), (true, vertices_322), (true, vertices_84), (true, vertices_324), (true, vertices_88), (true, vertices_360), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 16 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_903) then 14 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_360) then 18 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_903), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 2 4 5 7 360
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 376
cert_cover_5 4 1 2 3 4 5 56 376 3
cert_coverFacet 5 872
cert_cover_5 5 1 2 4 5 8 360 872 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0175

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_multi_six_0176.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0176

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 940, 120, 872, 496, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 104, 808, 584, 112, 176, 336, 400, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_940, vertices_120, vertices_872, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_808, vertices_584, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_524), (true, vertices_104), (true, vertices_808), (true, vertices_584), (true, vertices_112), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 7 14 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_647) then 8 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_181) then 9 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 17 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_808) then 15 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_416) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inl 1
  | 8 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 940 44 3
cert_row_4 2 1 2 4 6 7 940 44 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 8 1 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 940
cert_cover_2 1 2 1 4 6 44 940 3
cert_coverFacet 2 120
cert_cover_2 2 3 2 4 5 56 120 3
cert_coverFacet 3 872
cert_cover 3 5 2 2 4 3 1 7 4 104 872 808 44 940 6
cert_coverFacet 4 496
cert_cover_5 4 3 3 4 5 6 112 496 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0176

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_multi_six_0177.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0177

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 361, 993, 94, 838, 340, 916, 440, 344, 7, 11, 515, 53, 133, 41, 73, 353, 161, 577, 641, 30, 70, 518, 74, 578, 84, 148, 276, 324, 644, 772, 56, 88, 280, 296, 328, 176, 336, 400, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_993, vertices_94, vertices_838, vertices_340, vertices_916, vertices_440, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_353, vertices_161, vertices_577, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_993), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 17 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_647) then 10 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_993) then 20 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
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
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_993), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
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
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0177

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_multi_six_0178.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0178

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 718, 790, 338, 962, 692, 816, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 518, 74, 82, 274, 706, 322, 770, 140, 52, 532, 164, 644, 200, 304, 560, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_718, vertices_790, vertices_338, vertices_962, vertices_692, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_82, vertices_274, vertices_706, vertices_322, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_274), (true, vertices_706), (true, vertices_322), (true, vertices_770), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_91) then 9 else
  if p.val = (false, vertices_173) then 13 else
  if p.val = (false, vertices_457) then 15 else
  if p.val = (false, vertices_369) then 17 else
  if p.val = (false, vertices_929) then 19 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_706) then 10 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 22 3
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 0 1 2 5 6 718 14 3
cert_row_4 3 0 1 2 5 8 718 14 3
cert_rows
cert_pivot_2 7 3 6 1
cert_heightProof 4
cert_coverFacet 0 718
cert_cover_2 0 1 0 2 5 14 718 3
cert_coverFacet 1 790
cert_cover_5 1 0 0 1 3 7 22 790 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 962
cert_cover 3 6 1 0 5 3 0 7 2 706 962 706 14 718 5
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0178

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_multi_six_0179.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0179

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 881, 929, 142, 598, 902, 842, 394, 692, 27, 45, 73, 137, 49, 81, 161, 801, 321, 385, 14, 22, 134, 518, 74, 138, 266, 82, 578, 386, 770, 140, 52, 532, 164, 644, 328, 392, 560, 592, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_881, vertices_929, vertices_142, vertices_598, vertices_902, vertices_842, vertices_394, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_801, vertices_321, vertices_385, vertices_14, vertices_22, vertices_134, vertices_518, vertices_74, vertices_138, vertices_266, vertices_82, vertices_578, vertices_386, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_328, vertices_392, vertices_560, vertices_592, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_881), (false, vertices_929), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_644)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 14 16 17 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_173) then 13 else
  if p.val = (false, vertices_457) then 15 else
  if p.val = (false, vertices_881) then 18 else
  if p.val = (false, vertices_929) then 19 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
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
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_881), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
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
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0179

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_multi_six_0180.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0180

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 881, 929, 270, 598, 902, 842, 396, 692, 27, 45, 73, 137, 49, 81, 161, 801, 321, 385, 14, 22, 262, 518, 74, 266, 82, 578, 770, 140, 268, 52, 532, 164, 388, 644, 328, 392, 560, 592, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_881, vertices_929, vertices_270, vertices_598, vertices_902, vertices_842, vertices_396, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_801, vertices_321, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_266, vertices_82, vertices_578, vertices_770, vertices_140, vertices_268, vertices_52, vertices_532, vertices_164, vertices_388, vertices_644, vertices_328, vertices_392, vertices_560, vertices_592, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_881), (false, vertices_929), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_532), (true, vertices_388), (true, vertices_644)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 14 16 17 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_173) then 13 else
  if p.val = (false, vertices_457) then 15 else
  if p.val = (false, vertices_881) then 18 else
  if p.val = (false, vertices_929) then 19 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
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
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_881), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
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
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0180

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_multi_six_0181.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0181

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 590, 774, 684, 900, 888, 944, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 262, 518, 74, 578, 770, 44, 524, 164, 388, 644, 772, 56, 88, 552, 584, 176, 816, 336, 400, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_774, vertices_684, vertices_900, vertices_888, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_578, vertices_770, vertices_44, vertices_524, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_816, vertices_336, vertices_400, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_524), (true, vertices_644), (true, vertices_772), (true, vertices_552), (true, vertices_584), (true, vertices_816), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_181) then 10 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 888 56 3
cert_row_4 3 2 3 4 5 8 888 56 3
cert_rows
cert_pivot_2 0 1 7 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 888
cert_cover_2 4 3 2 4 5 56 888 3
cert_coverFacet 5 944
cert_cover 5 6 3 3 4 3 2 7 4 176 944 816 56 888 5
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0181

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_multi_six_0182.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0182

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 181, 465, 590, 646, 898, 684, 888, 944, 7, 27, 67, 259, 53, 133, 81, 145, 321, 385, 14, 134, 518, 74, 578, 386, 642, 770, 44, 524, 164, 644, 56, 88, 552, 584, 176, 816, 336, 400, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_646, vertices_898, vertices_684, vertices_888, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_134, vertices_518, vertices_74, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_816, vertices_336, vertices_400, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_642), (true, vertices_524), (true, vertices_644), (true, vertices_552), (true, vertices_584), (true, vertices_816), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_181) then 10 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 888 56 3
cert_row_4 3 2 3 4 5 8 888 56 3
cert_rows
cert_pivot_2 0 1 7 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 888
cert_cover_2 4 3 2 4 5 56 888 3
cert_coverFacet 5 944
cert_cover 5 6 3 3 4 3 2 7 4 176 944 816 56 888 5
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0182

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_multi_six_0183.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0183

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 437, 681, 94, 454, 706, 340, 824, 856, 992, 7, 11, 515, 53, 133, 41, 521, 161, 641, 30, 70, 134, 74, 194, 578, 642, 84, 276, 324, 388, 56, 88, 792, 552, 584, 304, 336, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_437, vertices_681, vertices_94, vertices_454, vertices_706, vertices_340, vertices_824, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_521, vertices_161, vertices_641, vertices_30, vertices_70, vertices_134, vertices_74, vertices_194, vertices_578, vertices_642, vertices_84, vertices_276, vertices_324, vertices_388, vertices_56, vertices_88, vertices_792, vertices_552, vertices_584, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_437), (false, vertices_681), (true, vertices_70), (true, vertices_194), (true, vertices_84), (true, vertices_324), (true, vertices_88), (true, vertices_792), (true, vertices_336), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_437) then 19 else
  if p.val = (false, vertices_681) then 16 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_792) then 17 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_437), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 4 5 6 7 8 992 416 1
cert_row_2 1 2 3 7 8 792
cert_row_2 2 0 1 2 3 30
cert_row_4 3 0 1 5 6 7 454 70 3
cert_rows
cert_pivot_2 4 8 2 0
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 5 30 94 3
cert_coverFacet 1 454
cert_cover_5 1 3 0 1 5 6 70 454 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 340
cert_cover_2 3 3 1 5 7 84 340 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0183

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_multi_six_0184.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0184

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 451, 437, 849, 590, 710, 684, 824, 600, 992, 7, 27, 67, 131, 53, 133, 81, 273, 321, 385, 14, 582, 134, 74, 194, 44, 524, 164, 644, 56, 88, 536, 552, 584, 304, 592, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_451, vertices_437, vertices_849, vertices_590, vertices_710, vertices_684, vertices_824, vertices_600, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_53, vertices_133, vertices_81, vertices_273, vertices_321, vertices_385, vertices_14, vertices_582, vertices_134, vertices_74, vertices_194, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_304, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_451), (false, vertices_437), (false, vertices_849), (true, vertices_582), (true, vertices_524), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_672), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 9 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_437) then 17 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_582) then 10 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_437), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 582 710 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 600
cert_cover_2 4 3 2 5 8 88 600 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0184

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_multi_six_0185.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0185

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 437, 809, 94, 842, 962, 724, 632, 816, 912, 7, 11, 131, 53, 133, 41, 265, 289, 385, 30, 70, 74, 266, 194, 834, 386, 84, 148, 196, 56, 88, 552, 584, 776, 304, 560, 592, 400, 656, 784, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_437, vertices_809, vertices_94, vertices_842, vertices_962, vertices_724, vertices_632, vertices_816, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_133, vertices_41, vertices_265, vertices_289, vertices_385, vertices_30, vertices_70, vertices_74, vertices_266, vertices_194, vertices_834, vertices_386, vertices_84, vertices_148, vertices_196, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_304, vertices_560, vertices_592, vertices_400, vertices_656, vertices_784, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_437), (false, vertices_809), (true, vertices_74), (true, vertices_834), (true, vertices_84), (true, vertices_88), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_784), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 10 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_437) then 19 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_834) then 15 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_88) then 2 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_437), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0185

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_multi_six_0186.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0186

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 805, 625, 206, 706, 898, 444, 728, 944, 7, 27, 67, 259, 37, 261, 49, 81, 545, 577, 769, 14, 134, 74, 194, 578, 386, 642, 770, 60, 140, 292, 388, 88, 152, 200, 432, 560, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_805, vertices_625, vertices_206, vertices_706, vertices_898, vertices_444, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_577, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_60, vertices_140, vertices_292, vertices_388, vertices_88, vertices_152, vertices_200, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_625), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_152), (true, vertices_200), (true, vertices_432), (true, vertices_656), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_805) then 10 else
  if p.val = (false, vertices_625) then 17 else
  if p.val = (true, vertices_194) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 1 2 3 6 4 444 60 3
cert_row_4 2 1 2 3 6 7 444 60 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 444
cert_cover_2 3 2 1 3 6 60 444 3
cert_coverFacet 4 728
cert_cover_5 4 3 2 3 5 6 88 728 3
cert_coverFacet 5 944
cert_cover 5 6 2 3 4 3 1 8 3 432 944 432 60 444 6
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0186

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_multi_six_0187.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0187

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 835, 805, 625, 206, 450, 444, 728, 944, 960, 7, 27, 67, 259, 37, 261, 49, 81, 545, 577, 769, 14, 134, 74, 194, 322, 386, 60, 140, 292, 388, 88, 152, 200, 432, 560, 592, 656, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_805, vertices_625, vertices_206, vertices_450, vertices_444, vertices_728, vertices_944, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_577, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_322, vertices_386, vertices_60, vertices_140, vertices_292, vertices_388, vertices_88, vertices_152, vertices_200, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_625), (true, vertices_194), (true, vertices_140), (true, vertices_152), (true, vertices_200), (true, vertices_432), (true, vertices_656), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_391) then 9 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_805) then 10 else
  if p.val = (false, vertices_625) then 17 else
  if p.val = (true, vertices_194) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_200) then 3 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_656) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 1 2 3 6 4 444 60 3
cert_row_4 2 1 2 3 6 7 444 60 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 444
cert_cover_2 2 2 1 3 6 60 444 3
cert_coverFacet 3 728
cert_cover_5 3 3 2 3 5 6 88 728 3
cert_coverFacet 4 944
cert_cover 4 6 2 3 4 3 1 8 3 432 944 432 60 444 6
cert_coverFacet 5 960
cert_cover_2 5 6 5 7 8 448 960 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0187

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_multi_six_0188.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0188

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 881, 929, 398, 598, 902, 842, 692, 27, 45, 73, 137, 49, 81, 161, 801, 321, 385, 14, 22, 390, 518, 74, 266, 82, 578, 770, 140, 52, 532, 164, 644, 328, 392, 560, 592, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_881, vertices_929, vertices_398, vertices_598, vertices_902, vertices_842, vertices_692] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_801, vertices_321, vertices_385, vertices_14, vertices_22, vertices_390, vertices_518, vertices_74, vertices_266, vertices_82, vertices_578, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_328, vertices_392, vertices_560, vertices_592, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_881), (false, vertices_929), (true, vertices_390), (true, vertices_518), (true, vertices_266), (true, vertices_578), (true, vertices_770), (true, vertices_532), (true, vertices_644)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 12 14 15 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_91) then 7 else
  if p.val = (false, vertices_173) then 11 else
  if p.val = (false, vertices_457) then 13 else
  if p.val = (false, vertices_881) then 16 else
  if p.val = (false, vertices_929) then 17 else
  if p.val = (true, vertices_390) then 8 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_644) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inl 4
  | 16 => Sum.inr ⟨(false, vertices_881), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_2 1 0 1 6 7 390
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 598
cert_cover_5 1 2 0 1 3 5 22 598 3
cert_coverFacet 2 902
cert_cover_5 2 1 0 1 6 8 390 902 3
cert_coverFacet 3 842
cert_cover_5 3 0 0 2 5 7 74 842 3
cert_coverFacet 4 692
cert_cover_5 4 3 1 3 4 6 52 692 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0188

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_multi_six_0189.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0189

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 429, 713, 625, 929, 206, 406, 850, 962, 820, 27, 45, 73, 137, 49, 81, 417, 545, 577, 641, 14, 22, 134, 74, 82, 274, 194, 834, 386, 140, 52, 276, 292, 388, 200, 560, 592, 784, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_429, vertices_713, vertices_625, vertices_929, vertices_206, vertices_406, vertices_850, vertices_962, vertices_820] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_417, vertices_545, vertices_577, vertices_641, vertices_14, vertices_22, vertices_134, vertices_74, vertices_82, vertices_274, vertices_194, vertices_834, vertices_386, vertices_140, vertices_52, vertices_276, vertices_292, vertices_388, vertices_200, vertices_560, vertices_592, vertices_784, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_429), (false, vertices_713), (false, vertices_625), (false, vertices_929), (true, vertices_134), (true, vertices_274), (true, vertices_194), (true, vertices_834), (true, vertices_386), (true, vertices_276), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 11 13 15 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_91) then 7 else
  if p.val = (false, vertices_429) then 16 else
  if p.val = (false, vertices_713) then 12 else
  if p.val = (false, vertices_625) then 14 else
  if p.val = (false, vertices_929) then 17 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_834) then 8 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_784) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 15 => Sum.inl 4
  | 16 => Sum.inr ⟨(false, vertices_429), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 0 5 7 8 834
cert_row_4 2 0 1 3 6 7 406 22 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 406
cert_cover_5 1 2 0 1 3 6 22 406 3
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 82 850 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0189

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_multi_six_0193.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0193

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 963, 805, 369, 206, 188, 676, 472, 944, 7, 27, 67, 643, 37, 517, 49, 81, 289, 321, 769, 14, 134, 74, 194, 60, 140, 164, 548, 644, 88, 152, 200, 176, 304, 336, 400, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_963, vertices_805, vertices_369, vertices_206, vertices_188, vertices_676, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_643, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_963), (false, vertices_805), (false, vertices_369), (true, vertices_140), (true, vertices_164), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 7 9 14 16 17 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_963) then 18 else
  if p.val = (false, vertices_805) then 8 else
  if p.val = (false, vertices_369) then 15 else
  if p.val = (true, vertices_140) then 0 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_200) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_672) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inl 1
  | 8 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inr ⟨(false, vertices_963), by decide +kernel⟩
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 188
cert_cover_5 1 1 1 2 3 6 60 188 3
cert_coverFacet 2 676
cert_cover_2 2 4 1 6 8 164 676 3
cert_coverFacet 3 472
cert_cover_5 3 2 2 3 5 6 88 472 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0193

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_multi_six_0198.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0198

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 835, 181, 901, 465, 590, 684, 888, 944, 7, 27, 67, 515, 53, 133, 517, 81, 145, 321, 385, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 552, 584, 176, 816, 336, 400, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_835, vertices_181, vertices_901, vertices_465, vertices_590, vertices_684, vertices_888, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_816, vertices_336, vertices_400, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_524), (true, vertices_552), (true, vertices_584), (true, vertices_816), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 5 8 12 13 16 17 18 19 20
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 9 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 6 else
  if p.val = (false, vertices_835) then 7 else
  if p.val = (false, vertices_181) then 10 else
  if p.val = (false, vertices_901) then 11 else
  if p.val = (false, vertices_465) then 14 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_816) then 15 else
  if p.val = (true, vertices_672) then 4 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 5 => Sum.inl 0
  | 6 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inl 6
  | 19 => Sum.inl 7
  | 20 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 888 56 3
cert_row_4 3 2 3 4 5 8 888 56 3
cert_rows
cert_pivot_2 0 1 7 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 888
cert_cover_2 2 3 2 4 5 56 888 3
cert_coverFacet 3 944
cert_cover 3 6 3 3 4 3 2 7 4 176 944 816 56 888 5
noncomputable def coveringFacets : Fin 4 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3]
noncomputable def coveringProof (j : Fin 4) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (fun i => Fin.elim0 i))))) j

cert_certificate 4 4
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0198

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_multi_six_0199.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0199

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 465, 897, 590, 684, 888, 944, 7, 27, 67, 515, 53, 133, 81, 145, 321, 385, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 552, 584, 176, 816, 336, 400, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_465, vertices_897, vertices_590, vertices_684, vertices_888, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_816, vertices_336, vertices_400, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (false, vertices_897), (true, vertices_524), (true, vertices_552), (true, vertices_584), (true, vertices_816), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 5 12 13 16 17 18 19 20
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 9 else
  if p.val = (false, vertices_647) then 6 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_181) then 7 else
  if p.val = (false, vertices_465) then 14 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_816) then 15 else
  if p.val = (true, vertices_672) then 4 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 5 => Sum.inl 1
  | 6 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inl 6
  | 19 => Sum.inl 7
  | 20 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 888 56 3
cert_row_4 3 2 3 4 5 8 888 56 3
cert_rows
cert_pivot_2 0 1 7 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 888
cert_cover_2 2 3 2 4 5 56 888 3
cert_coverFacet 3 944
cert_cover 3 6 3 3 4 3 2 7 4 176 944 816 56 888 5
noncomputable def coveringFacets : Fin 4 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3]
noncomputable def coveringProof (j : Fin 4) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (fun i => Fin.elim0 i))))) j

cert_certificate 4 4
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0199

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_multi_six_0202.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0202

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 625, 961, 142, 458, 444, 856, 944, 7, 27, 67, 37, 133, 49, 81, 545, 193, 577, 641, 14, 134, 74, 138, 194, 60, 140, 164, 88, 280, 328, 392, 432, 560, 592, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_625, vertices_961, vertices_142, vertices_458, vertices_444, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_60, vertices_140, vertices_164, vertices_88, vertices_280, vertices_328, vertices_392, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_625), (false, vertices_961), (true, vertices_138), (true, vertices_140), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_432), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 12 13 16 17 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 7 else
  if p.val = (false, vertices_91) then 8 else
  if p.val = (false, vertices_677) then 11 else
  if p.val = (false, vertices_625) then 14 else
  if p.val = (false, vertices_961) then 18 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_432) then 15 else
  if p.val = (true, vertices_784) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 3 6 4 444 60 3
cert_row_4 2 1 2 3 6 7 444 60 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 444
cert_cover_2 2 2 1 3 6 60 444 3
cert_coverFacet 3 856
cert_cover_5 3 3 2 3 5 7 88 856 3
cert_coverFacet 4 944
cert_cover 4 6 2 3 4 3 1 8 3 432 944 432 60 444 6
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0202

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_multi_six_0204.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0204

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 707, 805, 625, 897, 206, 444, 728, 944, 7, 27, 67, 131, 37, 261, 49, 81, 545, 577, 385, 641, 769, 14, 134, 74, 194, 60, 140, 292, 388, 88, 152, 200, 432, 560, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_707, vertices_805, vertices_625, vertices_897, vertices_206, vertices_444, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_60, vertices_140, vertices_292, vertices_388, vertices_88, vertices_152, vertices_200, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_707), (false, vertices_805), (false, vertices_625), (false, vertices_897), (true, vertices_140), (true, vertices_152), (true, vertices_200), (true, vertices_432), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 5 12 13 16 17 18 19 20
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 9 else
  if p.val = (false, vertices_391) then 6 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_707) then 11 else
  if p.val = (false, vertices_805) then 7 else
  if p.val = (false, vertices_625) then 14 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_200) then 3 else
  if p.val = (true, vertices_432) then 15 else
  if p.val = (true, vertices_656) then 4 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 5 => Sum.inl 1
  | 6 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inl 5
  | 18 => Sum.inl 6
  | 19 => Sum.inl 7
  | 20 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 1 2 3 6 4 444 60 3
cert_row_4 2 1 2 3 6 7 444 60 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 444
cert_cover_2 1 2 1 3 6 60 444 3
cert_coverFacet 2 728
cert_cover_5 2 3 2 3 5 6 88 728 3
cert_coverFacet 3 944
cert_cover 3 6 2 3 4 3 1 8 3 432 944 432 60 444 6
noncomputable def coveringFacets : Fin 4 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3]
noncomputable def coveringProof (j : Fin 4) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (fun i => Fin.elim0 i))))) j

cert_certificate 4 4
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0204

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_multi_six_0207.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0207

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 903, 587, 181, 681, 94, 838, 468, 888, 944, 7, 11, 515, 53, 133, 41, 521, 161, 641, 30, 70, 774, 74, 578, 84, 148, 324, 388, 56, 88, 552, 584, 176, 816, 336, 400, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_903, vertices_587, vertices_181, vertices_681, vertices_94, vertices_838, vertices_468, vertices_888, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_521, vertices_161, vertices_641, vertices_30, vertices_70, vertices_774, vertices_74, vertices_578, vertices_84, vertices_148, vertices_324, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_816, vertices_336, vertices_400, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_903), (false, vertices_587), (false, vertices_181), (false, vertices_681), (true, vertices_70), (true, vertices_84), (true, vertices_324), (true, vertices_88), (true, vertices_816), (true, vertices_336), (true, vertices_400), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 9 13 15 17 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_903) then 11 else
  if p.val = (false, vertices_587) then 8 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_681) then 14 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_816) then 16 else
  if p.val = (true, vertices_336) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_832) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_903), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 7 468 84 3
cert_row_4 1 2 3 4 7 5 888 56 3
cert_row_4 2 2 3 4 7 8 888 56 3
cert_row_2 3 0 1 7 8 774
cert_row_2 4 0 1 2 3 30
cert_rows_2
cert_pivot 6 5 4 7 0
cert_heightProof 5
cert_coverFacet 0 94
cert_cover_5 0 4 0 1 2 5 30 94 3
cert_coverFacet 1 838
cert_cover_5 1 3 0 1 5 7 70 838 3
cert_coverFacet 2 468
cert_cover_5 2 0 1 3 5 6 84 468 3
cert_coverFacet 3 888
cert_cover_2 3 3 2 4 7 56 888 3
cert_coverFacet 4 944
cert_cover 4 6 3 3 4 3 2 7 4 176 944 816 56 888 7
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 5 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0207

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_multi_six_0208.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0208

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 963, 805, 625, 206, 444, 728, 944, 7, 27, 67, 387, 37, 261, 49, 81, 545, 577, 769, 14, 134, 74, 194, 60, 140, 292, 388, 88, 152, 200, 432, 560, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_963, vertices_805, vertices_625, vertices_206, vertices_444, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_387, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_577, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_60, vertices_140, vertices_292, vertices_388, vertices_88, vertices_152, vertices_200, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_963), (false, vertices_805), (false, vertices_625), (true, vertices_140), (true, vertices_152), (true, vertices_200), (true, vertices_432), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 4 6 11 14 15 17 18 19
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 7 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_91) then 8 else
  if p.val = (false, vertices_963) then 16 else
  if p.val = (false, vertices_805) then 5 else
  if p.val = (false, vertices_625) then 12 else
  if p.val = (true, vertices_140) then 0 else
  if p.val = (true, vertices_152) then 1 else
  if p.val = (true, vertices_200) then 2 else
  if p.val = (true, vertices_432) then 13 else
  if p.val = (true, vertices_656) then 3 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 4 => Sum.inl 1
  | 5 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 6 => Sum.inl 2
  | 7 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 14 => Sum.inl 4
  | 15 => Sum.inl 5
  | 16 => Sum.inr ⟨(false, vertices_963), by decide +kernel⟩
  | 17 => Sum.inl 6
  | 18 => Sum.inl 7
  | 19 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 1 2 3 6 4 444 60 3
cert_row_4 2 1 2 3 6 7 444 60 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 444
cert_cover_2 1 2 1 3 6 60 444 3
cert_coverFacet 2 728
cert_cover_5 2 3 2 3 5 6 88 728 3
cert_coverFacet 3 944
cert_cover 3 6 2 3 4 3 1 8 3 432 944 432 60 444 6
noncomputable def coveringFacets : Fin 4 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3]
noncomputable def coveringProof (j : Fin 4) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (fun i => Fin.elim0 i))))) j

cert_certificate 4 4
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0208

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 451, 85, 553, 369, 929, 206, 668, 852, 964, 824, 7, 11, 67, 131, 21, 69, 41, 521, 49, 81, 289, 545, 321, 385, 641, 14, 70, 138, 194, 28, 140, 84, 532, 196, 836, 644, 56, 536, 552, 648, 304, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_451, vertices_85, vertices_553, vertices_369, vertices_929, vertices_206, vertices_668, vertices_852, vertices_964, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_14, vertices_70, vertices_138, vertices_194, vertices_28, vertices_140, vertices_84, vertices_532, vertices_196, vertices_836, vertices_644, vertices_56, vertices_536, vertices_552, vertices_648, vertices_304, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_451), (false, vertices_85), (false, vertices_553), (false, vertices_369), (false, vertices_929), (true, vertices_140), (true, vertices_532), (true, vertices_196), (true, vertices_836), (true, vertices_644), (true, vertices_536), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_451) then 11 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_553) then 2 else
  if p.val = (false, vertices_369) then 17 else
  if p.val = (false, vertices_929) then 19 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_836) then 14 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_784) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 5 7 8 836
cert_row_4 2 1 2 3 6 8 668 28 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 668
cert_cover_5 1 2 1 2 3 6 28 668 3
cert_coverFacet 2 852
cert_cover_5 2 1 1 3 5 7 84 852 3
cert_coverFacet 3 964
cert_cover_5 3 1 1 5 6 7 196 964 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0012

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 661, 809, 561, 78, 842, 962, 92, 468, 376, 944, 7, 11, 131, 21, 133, 41, 521, 49, 529, 545, 641, 14, 70, 74, 522, 194, 834, 642, 28, 76, 84, 148, 196, 56, 88, 296, 328, 776, 304, 560, 336, 400, 656, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_661, vertices_809, vertices_561, vertices_78, vertices_842, vertices_962, vertices_92, vertices_468, vertices_376, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_529, vertices_545, vertices_641, vertices_14, vertices_70, vertices_74, vertices_522, vertices_194, vertices_834, vertices_642, vertices_28, vertices_76, vertices_84, vertices_148, vertices_196, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_400, vertices_656, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_661), (false, vertices_809), (false, vertices_561), (true, vertices_74), (true, vertices_834), (true, vertices_76), (true, vertices_84), (true, vertices_88), (true, vertices_328), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_661) then 13 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_834) then 17 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 468
cert_cover_5 4 1 1 3 5 6 84 468 3
cert_coverFacet 5 376
cert_cover_5 5 2 2 3 4 5 56 376 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0013

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0014.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0014

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 533, 617, 689, 833, 78, 454, 220, 916, 248, 992, 7, 11, 259, 21, 517, 41, 73, 49, 529, 545, 321, 577, 769, 14, 70, 262, 74, 322, 28, 76, 148, 532, 196, 388, 772, 56, 216, 104, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_533, vertices_617, vertices_689, vertices_833, vertices_78, vertices_454, vertices_220, vertices_916, vertices_248, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_73, vertices_49, vertices_529, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_322, vertices_28, vertices_76, vertices_148, vertices_532, vertices_196, vertices_388, vertices_772, vertices_56, vertices_216, vertices_104, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_533), (false, vertices_617), (false, vertices_689), (false, vertices_833), (true, vertices_70), (true, vertices_76), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_224), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_833) then 1 else
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
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
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
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0014

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0015.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 533, 809, 689, 78, 454, 220, 916, 248, 360, 992, 7, 11, 259, 21, 517, 41, 265, 49, 529, 545, 769, 14, 70, 262, 74, 322, 28, 76, 148, 532, 196, 388, 772, 56, 216, 104, 296, 328, 176, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_533, vertices_809, vertices_689, vertices_78, vertices_454, vertices_220, vertices_916, vertices_248, vertices_360, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_322, vertices_28, vertices_76, vertices_148, vertices_532, vertices_196, vertices_388, vertices_772, vertices_56, vertices_216, vertices_104, vertices_296, vertices_328, vertices_176, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_533), (false, vertices_809), (false, vertices_689), (true, vertices_70), (true, vertices_76), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_104), (true, vertices_224), (true, vertices_352), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_216) then 18 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_coverFacet 5 360
cert_cover_2 5 4 2 5 7 104 360 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0015

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0016.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 213, 665, 897, 334, 812, 372, 568, 752, 992, 7, 11, 67, 259, 21, 69, 25, 521, 145, 193, 385, 641, 769, 14, 70, 266, 322, 44, 268, 52, 84, 292, 324, 56, 536, 552, 776, 112, 560, 208, 656, 736, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_213, vertices_665, vertices_897, vertices_334, vertices_812, vertices_372, vertices_568, vertices_752, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_521, vertices_145, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_268, vertices_52, vertices_84, vertices_292, vertices_324, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_736, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_665), (false, vertices_897), (true, vertices_268), (true, vertices_292), (true, vertices_324), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_736), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_451) then 12 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_665) then 17 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_736) then 20 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 6 8 736
cert_row_4 1 0 1 2 5 7 334 14 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 14 334 3
cert_coverFacet 1 812
cert_cover_5 1 2 1 2 4 7 44 812 3
cert_coverFacet 2 372
cert_cover_5 2 3 1 3 4 5 52 372 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 752
cert_cover_5 4 0 3 4 5 6 112 752 3
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 7 736 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0016

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0660 : Certifies 660 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0172.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0661 : Certifies 661 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0173.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0662 : Certifies 662 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0174.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0663 : Certifies 663 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0175.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0664 : Certifies 664 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0176.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0665 : Certifies 665 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0177.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0666 : Certifies 666 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0178.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0667 : Certifies 667 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0179.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0668 : Certifies 668 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0180.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0669 : Certifies 669 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0181.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0670 : Certifies 670 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0182.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0671 : Certifies 671 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0183.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0672 : Certifies 672 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0184.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0673 : Certifies 673 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0185.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0674 : Certifies 674 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0186.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0675 : Certifies 675 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0187.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0676 : Certifies 676 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0188.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0677 : Certifies 677 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0189.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0678 : Certifies 678 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0193.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0679 : Certifies 679 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0198.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0680 : Certifies 680 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0199.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0681 : Certifies 681 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0202.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0682 : Certifies 682 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0204.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0683 : Certifies 683 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0207.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0684 : Certifies 684 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0208.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0685 : Certifies 685 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0686 : Certifies 686 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0687 : Certifies 687 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0014.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0688 : Certifies 688 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0015.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0689 : Certifies 689 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0016.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B022 (j : Fin 30) :
    Certifies (660 + j.val) := by
  fin_cases j
  · exact projection_0660
  · exact projection_0661
  · exact projection_0662
  · exact projection_0663
  · exact projection_0664
  · exact projection_0665
  · exact projection_0666
  · exact projection_0667
  · exact projection_0668
  · exact projection_0669
  · exact projection_0670
  · exact projection_0671
  · exact projection_0672
  · exact projection_0673
  · exact projection_0674
  · exact projection_0675
  · exact projection_0676
  · exact projection_0677
  · exact projection_0678
  · exact projection_0679
  · exact projection_0680
  · exact projection_0681
  · exact projection_0682
  · exact projection_0683
  · exact projection_0684
  · exact projection_0685
  · exact projection_0686
  · exact projection_0687
  · exact projection_0688
  · exact projection_0689

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
