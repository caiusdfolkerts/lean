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
/- Source: ProjectionCertificates/R_one_six_1233.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1233

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 451, 805, 369, 897, 206, 188, 676, 472, 944, 7, 27, 67, 131, 37, 517, 49, 81, 289, 321, 385, 641, 769, 14, 134, 74, 194, 60, 140, 164, 548, 644, 88, 152, 200, 176, 304, 336, 400, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_451, vertices_805, vertices_369, vertices_897, vertices_206, vertices_188, vertices_676, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_451), (false, vertices_805), (false, vertices_369), (false, vertices_897), (true, vertices_140), (true, vertices_164), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 15 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_647) then 9 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_805) then 10 else
  if p.val = (false, vertices_369) then 17 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1233

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1242.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1242

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 181, 901, 681, 94, 330, 468, 376, 808, 944, 7, 11, 259, 53, 133, 261, 41, 521, 161, 641, 769, 30, 70, 74, 266, 322, 84, 148, 324, 388, 56, 88, 296, 552, 328, 776, 176, 304, 336, 400, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_181, vertices_901, vertices_681, vertices_94, vertices_330, vertices_468, vertices_376, vertices_808, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_133, vertices_261, vertices_41, vertices_521, vertices_161, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_266, vertices_322, vertices_84, vertices_148, vertices_324, vertices_388, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_181), (false, vertices_901), (false, vertices_681), (true, vertices_74), (true, vertices_84), (true, vertices_88), (true, vertices_296), (true, vertices_328), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_901) then 15 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_88) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 468
cert_cover_5 2 1 1 3 5 6 84 468 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 808
cert_cover_2 4 4 2 7 8 296 808 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1242

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1243.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1243

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 181, 901, 681, 94, 330, 468, 568, 856, 944, 7, 11, 259, 53, 133, 261, 41, 521, 161, 641, 769, 30, 70, 74, 266, 322, 84, 148, 324, 388, 56, 88, 536, 552, 328, 776, 176, 560, 336, 400, 784, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_181, vertices_901, vertices_681, vertices_94, vertices_330, vertices_468, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_133, vertices_261, vertices_41, vertices_521, vertices_161, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_266, vertices_322, vertices_84, vertices_148, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_336, vertices_400, vertices_784, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_181), (false, vertices_901), (false, vertices_681), (true, vertices_74), (true, vertices_84), (true, vertices_88), (true, vertices_536), (true, vertices_328), (true, vertices_560), (true, vertices_336), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_901) then 15 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_88) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_784) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 468
cert_cover_5 2 1 1 3 5 6 84 468 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 856
cert_cover_5 4 2 2 3 5 7 88 856 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1243

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1244.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1244

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 835, 181, 901, 465, 590, 684, 632, 944, 848, 7, 27, 67, 515, 53, 133, 517, 81, 145, 321, 385, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 552, 584, 176, 560, 336, 592, 400, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_835, vertices_181, vertices_901, vertices_465, vertices_590, vertices_684, vertices_632, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_524), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 9 else
  if p.val = (false, vertices_835) then 10 else
  if p.val = (false, vertices_181) then 13 else
  if p.val = (false, vertices_901) then 14 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 15 => Sum.inl 2
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 632
cert_cover_5 2 2 2 3 4 5 56 632 3
cert_coverFacet 3 944
cert_cover_5 3 3 3 4 6 7 176 944 3
cert_coverFacet 4 848
cert_cover_2 4 5 3 7 8 336 848 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1244

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1245.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1245

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 835, 181, 901, 465, 590, 684, 568, 856, 944, 7, 27, 67, 515, 53, 133, 517, 81, 145, 321, 385, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 536, 552, 584, 176, 560, 336, 400, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_835, vertices_181, vertices_901, vertices_465, vertices_590, vertices_684, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_176, vertices_560, vertices_336, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_524), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 9 else
  if p.val = (false, vertices_835) then 10 else
  if p.val = (false, vertices_181) then 13 else
  if p.val = (false, vertices_901) then 14 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 15 => Sum.inl 2
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 568
cert_cover_2 2 3 2 4 8 56 568 3
cert_coverFacet 3 856
cert_cover_5 3 2 2 3 5 7 88 856 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1245

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1246.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1246

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 465, 897, 590, 684, 632, 944, 848, 7, 27, 67, 515, 53, 133, 81, 145, 321, 385, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 552, 584, 176, 560, 336, 592, 400, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_465, vertices_897, vertices_590, vertices_684, vertices_632, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (false, vertices_897), (true, vertices_524), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 8 15 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_647) then 9 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_181) then 10 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 2
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 632
cert_cover_5 2 2 2 3 4 5 56 632 3
cert_coverFacet 3 944
cert_cover_5 3 3 3 4 6 7 176 944 3
cert_coverFacet 4 848
cert_cover_2 4 5 3 7 8 336 848 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1246

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1247.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1247

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 139, 899, 109, 597, 425, 865, 126, 662, 186, 496, 976, 11, 131, 515, 13, 69, 517, 41, 137, 97, 289, 577, 385, 769, 14, 22, 518, 58, 138, 146, 642, 108, 84, 532, 168, 112, 176, 464, 592, 656, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_139, vertices_899, vertices_109, vertices_597, vertices_425, vertices_865, vertices_126, vertices_662, vertices_186, vertices_496, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_515, vertices_13, vertices_69, vertices_517, vertices_41, vertices_137, vertices_97, vertices_289, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_518, vertices_58, vertices_138, vertices_146, vertices_642, vertices_108, vertices_84, vertices_532, vertices_168, vertices_112, vertices_176, vertices_464, vertices_592, vertices_656, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_139), (false, vertices_899), (false, vertices_109), (false, vertices_597), (false, vertices_425), (false, vertices_865), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_112), (true, vertices_176), (true, vertices_464), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 10 13 15 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 7 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_899) then 8 else
  if p.val = (false, vertices_109) then 11 else
  if p.val = (false, vertices_597) then 12 else
  if p.val = (false, vertices_425) then 14 else
  if p.val = (false, vertices_865) then 18 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_58) then 9 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_112) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_464) then 16 else
  if p.val = (true, vertices_656) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
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
cert_coverFacet 2 186
cert_cover 2 3 1 0 2 3 0 6 2 58 186 58 14 126 3
cert_coverFacet 3 496
cert_cover_5 3 0 3 4 5 6 112 496 3
cert_coverFacet 4 976
cert_cover_5 4 0 3 5 6 8 464 976 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1247

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1248.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1248

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 433, 849, 654, 598, 202, 962, 820, 932, 27, 45, 73, 137, 49, 81, 273, 161, 321, 385, 14, 22, 518, 74, 138, 82, 194, 578, 642, 140, 52, 532, 164, 804, 644, 200, 304, 592, 784, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_433, vertices_849, vertices_654, vertices_598, vertices_202, vertices_962, vertices_820, vertices_932] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_273, vertices_161, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_532, vertices_164, vertices_804, vertices_644, vertices_200, vertices_304, vertices_592, vertices_784, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_433), (false, vertices_849), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_532), (true, vertices_804), (true, vertices_644), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 14 10 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_91) then 9 else
  if p.val = (false, vertices_173) then 12 else
  if p.val = (false, vertices_457) then 13 else
  if p.val = (false, vertices_433) then 17 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_804) then 15 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 0 1 3 5 8 598 22 3
cert_row_4 3 0 5 6 7 8 962 194 3
cert_rows
cert_pivot_2 4 2 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 598
cert_cover_5 1 2 0 1 3 5 22 598 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 3 0 5 6 7 194 962 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 932
cert_cover_5 5 0 1 4 6 7 164 932 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1248

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1249.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1249

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 173, 457, 369, 929, 206, 662, 850, 962, 820, 676, 27, 45, 73, 137, 49, 81, 161, 289, 321, 385, 14, 22, 134, 74, 82, 530, 194, 834, 642, 140, 52, 532, 164, 548, 644, 200, 304, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_206, vertices_662, vertices_850, vertices_962, vertices_820, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_134, vertices_74, vertices_82, vertices_530, vertices_194, vertices_834, vertices_642, vertices_140, vertices_52, vertices_532, vertices_164, vertices_548, vertices_644, vertices_200, vertices_304, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_134), (true, vertices_530), (true, vertices_194), (true, vertices_834), (true, vertices_642), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_91) then 9 else
  if p.val = (false, vertices_173) then 13 else
  if p.val = (false, vertices_457) then 15 else
  if p.val = (false, vertices_369) then 17 else
  if p.val = (false, vertices_929) then 19 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_834) then 10 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 0 5 7 8 834
cert_row_4 2 0 1 3 6 8 662 22 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 22 662 3
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 82 850 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1249

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1250.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1250

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 369, 961, 654, 714, 188, 676, 472, 944, 7, 27, 67, 37, 517, 49, 81, 289, 321, 577, 769, 14, 518, 74, 650, 578, 60, 140, 164, 548, 644, 88, 152, 200, 176, 304, 336, 400, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_369, vertices_961, vertices_654, vertices_714, vertices_188, vertices_676, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_650, vertices_578, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_369), (false, vertices_961), (true, vertices_650), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 8 17 11 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_583) then 9 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 10 else
  if p.val = (false, vertices_369) then 14 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_650) then 16 else
  if p.val = (true, vertices_140) then 0 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_2 1 0 2 6 8 650
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 74 714 3
cert_coverFacet 2 188
cert_cover_5 2 0 1 2 3 6 60 188 3
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 472
cert_cover_5 4 2 2 3 5 6 88 472 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1250

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1251.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1251

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 654, 714, 188, 676, 472, 992, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 518, 74, 650, 578, 60, 140, 164, 548, 644, 88, 152, 200, 176, 336, 400, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_654, vertices_714, vertices_188, vertices_676, vertices_472, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_518, vertices_74, vertices_650, vertices_578, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_650), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_200), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 8 19 13 11 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_583) then 9 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_805) then 10 else
  if p.val = (false, vertices_433) then 12 else
  if p.val = (false, vertices_849) then 16 else
  if p.val = (true, vertices_650) then 18 else
  if p.val = (true, vertices_140) then 0 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_704) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 11 => Sum.inl 4
  | 12 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_650), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_2 1 0 2 6 8 650
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 74 714 3
cert_coverFacet 2 188
cert_cover_5 2 0 1 2 3 6 60 188 3
cert_coverFacet 3 676
cert_cover_2 3 4 1 6 8 164 676 3
cert_coverFacet 4 472
cert_cover_5 4 2 2 3 5 6 88 472 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1251

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1253.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1253

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 181, 901, 465, 782, 842, 684, 632, 944, 848, 7, 27, 67, 53, 133, 261, 81, 145, 321, 385, 14, 262, 74, 778, 322, 44, 524, 164, 644, 772, 56, 88, 552, 584, 176, 560, 336, 592, 400, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_181, vertices_901, vertices_465, vertices_782, vertices_842, vertices_684, vertices_632, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_74, vertices_778, vertices_322, vertices_44, vertices_524, vertices_164, vertices_644, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 10 19 13 8 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_327) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_181) then 9 else
  if p.val = (false, vertices_901) then 12 else
  if p.val = (false, vertices_465) then 16 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_552) then 1 else
  if p.val = (true, vertices_584) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_832) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inl 4
  | 9 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 74 842 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 632
cert_cover_5 3 2 2 3 4 5 56 632 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1253

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1254.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1254

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 835, 181, 901, 465, 590, 684, 376, 872, 944, 7, 27, 67, 515, 53, 133, 517, 81, 145, 321, 385, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 360, 552, 584, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_835, vertices_181, vertices_901, vertices_465, vertices_590, vertices_684, vertices_376, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_360, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_524), (true, vertices_360), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 14 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 8 else
  if p.val = (false, vertices_835) then 9 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_901) then 13 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_360) then 15 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_800) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_2 1 2 4 5 7 360
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 5 1 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 2 1 2 4 6 44 684 3
cert_coverFacet 2 376
cert_cover_5 2 1 2 3 4 5 56 376 3
cert_coverFacet 3 872
cert_cover_5 3 1 2 4 5 8 360 872 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1254

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1255.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1255

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 465, 897, 590, 684, 376, 872, 944, 7, 27, 67, 515, 53, 133, 81, 145, 321, 385, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 360, 552, 584, 176, 304, 336, 400, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_465, vertices_897, vertices_590, vertices_684, vertices_376, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_360, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (false, vertices_897), (true, vertices_524), (true, vertices_360), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 7 14 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_647) then 8 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_181) then 9 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_360) then 15 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_584) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_800) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inl 1
  | 8 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(true, vertices_360), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_2 1 2 4 5 7 360
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 5 1 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 2 1 2 4 6 44 684 3
cert_coverFacet 2 376
cert_cover_5 2 1 2 3 4 5 56 376 3
cert_coverFacet 3 872
cert_cover_5 3 1 2 4 5 8 360 872 3
cert_coverFacet 4 944
cert_cover_5 4 3 3 4 6 7 176 944 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1255

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1256.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1256

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 775, 651, 425, 241, 721, 865, 126, 662, 186, 364, 852, 263, 11, 515, 137, 265, 209, 97, 161, 289, 577, 641, 769, 14, 22, 518, 58, 138, 146, 642, 108, 268, 84, 532, 324, 772, 168, 296, 112, 176, 592, 656, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_775, vertices_651, vertices_425, vertices_241, vertices_721, vertices_865, vertices_126, vertices_662, vertices_186, vertices_364, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_11, vertices_515, vertices_137, vertices_265, vertices_209, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_518, vertices_58, vertices_138, vertices_146, vertices_642, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_592, vertices_656, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_775), (false, vertices_651), (false, vertices_425), (false, vertices_241), (false, vertices_721), (false, vertices_865), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_108), (true, vertices_84), (true, vertices_532), (true, vertices_324)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 5 12 14 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 6 else
  if p.val = (false, vertices_775) then 7 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_425) then 13 else
  if p.val = (false, vertices_241) then 15 else
  if p.val = (false, vertices_721) then 16 else
  if p.val = (false, vertices_865) then 18 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_58) then 11 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_108) then 8 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_324) then 4 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inl 1
  | 6 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 7 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1256

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1258.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1258

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 75, 835, 181, 617, 929, 94, 326, 340, 916, 696, 856, 7, 11, 67, 259, 53, 133, 41, 73, 161, 545, 577, 385, 769, 30, 70, 262, 74, 322, 84, 148, 276, 324, 388, 56, 88, 536, 552, 584, 176, 336, 656, 784, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_75, vertices_835, vertices_181, vertices_617, vertices_929, vertices_94, vertices_326, vertices_340, vertices_916, vertices_696, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_545, vertices_577, vertices_385, vertices_769, vertices_30, vertices_70, vertices_262, vertices_74, vertices_322, vertices_84, vertices_148, vertices_276, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_176, vertices_336, vertices_656, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_75), (false, vertices_835), (false, vertices_181), (false, vertices_617), (false, vertices_929), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_88), (true, vertices_536), (true, vertices_336), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_75) then 0 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_617) then 17 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 340
cert_cover_2 2 3 1 5 7 84 340 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 148 916 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1258

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1260.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1260

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 689, 849, 142, 902, 458, 188, 676, 344, 920, 7, 27, 67, 37, 261, 49, 81, 529, 545, 321, 769, 14, 134, 262, 74, 138, 322, 386, 60, 140, 164, 548, 644, 772, 88, 152, 280, 328, 392, 176, 336, 656, 784, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_689, vertices_849, vertices_142, vertices_902, vertices_458, vertices_188, vertices_676, vertices_344, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_769, vertices_14, vertices_134, vertices_262, vertices_74, vertices_138, vertices_322, vertices_386, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_328, vertices_392, vertices_176, vertices_336, vertices_656, vertices_784, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_689), (false, vertices_849), (true, vertices_134), (true, vertices_138), (true, vertices_386), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 134 138 386 140 164 644 152 280 328 392 896 327 91 63 805 689 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 2 3 6 7 8 920 152 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 2 0 2 5 6 74 458 3
cert_coverFacet 3 188
cert_cover_5 3 0 1 2 3 6 60 188 3
cert_coverFacet 4 676
cert_cover_2 4 4 1 6 8 164 676 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 920
cert_cover_5 6 3 2 3 6 7 152 920 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1260

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1261.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1261

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 428, 652, 376, 968, 432, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 140, 524, 164, 644, 56, 88, 296, 328, 584, 392, 648, 176, 304, 336, 400, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_428, vertices_652, vertices_376, vertices_968, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_140, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_140), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 337 1 140 524 296 328 584 392 648 304 416 647 181 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 428
cert_cover_5 1 1 1 2 4 6 44 428 3
cert_coverFacet 2 652
cert_cover_2 2 2 1 6 8 140 652 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 968
cert_cover_5 4 3 2 5 6 7 328 968 2
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1261

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1262.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1262

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 684, 120, 872, 496, 928, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 104, 552, 584, 112, 176, 336, 400, 352, 416, 672, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_684, vertices_120, vertices_872, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_112), (true, vertices_352), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 337 1 524 104 552 584 112 352 416 672 800 647 181 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 120
cert_cover_2 2 3 2 4 5 56 120 3
cert_coverFacet 3 872
cert_cover_5 3 2 2 4 5 7 104 872 3
cert_coverFacet 4 496
cert_cover_5 4 3 3 4 5 6 112 496 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1262

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1263.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1263

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 684, 376, 616, 432, 992, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 104, 552, 584, 176, 304, 336, 400, 352, 608, 416, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_684, vertices_376, vertices_616, vertices_432, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 337 1 524 104 552 584 304 352 608 416 672 647 181 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 376
cert_cover_5 2 2 2 3 4 5 56 376 3
cert_coverFacet 3 616
cert_cover_2 3 4 2 5 8 104 616 3
cert_coverFacet 4 432
cert_cover_2 4 4 3 6 7 176 432 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1263

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1264.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1264

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 684, 120, 232, 968, 496, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 104, 168, 200, 584, 648, 112, 176, 336, 400, 224, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_684, vertices_120, vertices_232, vertices_968, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_104, vertices_168, vertices_200, vertices_584, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_524), (true, vertices_104), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_112), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 337 1 524 104 168 200 584 648 112 224 448 647 181 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 5 6 7 8 968 200 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 120
cert_cover_2 2 3 2 4 5 56 120 3
cert_coverFacet 3 232
cert_cover_2 3 4 2 5 6 104 232 3
cert_coverFacet 4 968
cert_cover_5 4 2 2 5 6 7 200 968 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1264

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1265.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1265

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 684, 376, 424, 968, 432, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 524, 164, 644, 56, 88, 168, 296, 328, 584, 392, 648, 176, 304, 336, 400, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_684, vertices_376, vertices_424, vertices_968, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_168, vertices_296, vertices_328, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_524), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_416) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 337 1 524 168 296 328 584 392 648 304 416 647 181 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 376
cert_cover_5 2 2 2 3 4 5 56 376 3
cert_coverFacet 3 424
cert_cover_2 3 4 2 6 7 168 424 3
cert_coverFacet 4 968
cert_cover_5 4 3 2 5 6 7 328 968 2
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1265

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1266.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1266

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 556, 932, 120, 872, 496, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 524, 164, 548, 644, 56, 88, 104, 552, 584, 112, 176, 336, 400, 352, 416, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_556, vertices_932, vertices_120, vertices_872, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_524), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_112), (true, vertices_352), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 337 1 524 548 104 552 584 112 352 416 800 647 181 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 4 6 7 8 932 164 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 556
cert_cover_2 1 2 1 4 8 44 556 3
cert_coverFacet 2 932
cert_cover_5 2 1 1 4 6 7 164 932 3
cert_coverFacet 3 120
cert_cover_2 3 3 2 4 5 56 120 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1266

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1267.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1267

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 556, 932, 440, 344, 872, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 524, 164, 548, 644, 56, 88, 280, 296, 552, 328, 584, 176, 336, 400, 416, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_556, vertices_932, vertices_440, vertices_344, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_524, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_552, vertices_328, vertices_584, vertices_176, vertices_336, vertices_400, vertices_416, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_524), (true, vertices_548), (true, vertices_280), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 337 1 524 548 280 296 552 328 584 416 800 647 181 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 4 6 7 8 932 164 3
cert_row_4 2 2 3 4 6 7 440 56 3
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
cert_coverFacet 3 440
cert_cover_5 3 2 2 3 4 6 56 440 3
cert_coverFacet 4 344
cert_cover_2 4 3 2 5 7 88 344 3
cert_coverFacet 5 872
cert_cover_5 5 3 2 4 5 7 296 872 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1267

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1268.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1268

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 181, 337, 913, 590, 236, 708, 376, 432, 992, 7, 27, 67, 515, 53, 133, 81, 145, 273, 321, 641, 769, 14, 518, 74, 578, 44, 76, 164, 196, 580, 644, 56, 88, 104, 176, 304, 336, 400, 224, 352, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_236, vertices_708, vertices_376, vertices_432, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_76, vertices_164, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_104, vertices_176, vertices_304, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_76), (true, vertices_196), (true, vertices_580), (true, vertices_104), (true, vertices_304), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_181) then 12 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
cert_nodeAtPriority_41 0 337 1 76 196 580 104 304 224 352 416 704 647 181 91 835 913
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 236
cert_cover_5 1 1 1 2 4 5 44 236 3
cert_coverFacet 2 708
cert_cover_2 2 5 1 6 8 196 708 3
cert_coverFacet 3 376
cert_cover_5 3 2 2 3 4 5 56 376 3
cert_coverFacet 4 432
cert_cover_2 4 4 3 6 7 176 432 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1268

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1269.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1269

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 361, 929, 833, 94, 838, 340, 916, 120, 496, 7, 11, 515, 53, 133, 41, 73, 161, 289, 321, 577, 641, 769, 30, 70, 518, 74, 578, 84, 148, 276, 324, 644, 772, 56, 88, 104, 112, 176, 336, 400, 352, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_929, vertices_833, vertices_94, vertices_838, vertices_340, vertices_916, vertices_120, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_112, vertices_176, vertices_336, vertices_400, vertices_352, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_929), (false, vertices_833), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_112), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
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
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 340
cert_cover_2 2 3 1 5 7 84 340 3
cert_coverFacet 3 916
cert_cover_5 3 2 1 3 6 7 148 916 3
cert_coverFacet 4 120
cert_cover_2 4 3 2 4 5 56 120 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1269

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1270.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1270

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 361, 929, 833, 94, 838, 340, 916, 440, 344, 7, 11, 515, 53, 133, 41, 73, 161, 289, 321, 577, 641, 769, 30, 70, 518, 74, 578, 84, 148, 276, 324, 644, 772, 56, 88, 280, 296, 328, 176, 336, 400, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_929, vertices_833, vertices_94, vertices_838, vertices_340, vertices_916, vertices_440, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_929), (false, vertices_833), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
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
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1270

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1271.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1271

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 233, 961, 94, 838, 340, 916, 376, 432, 480, 7, 11, 515, 53, 133, 41, 73, 161, 193, 577, 641, 30, 70, 518, 74, 578, 84, 148, 276, 324, 644, 772, 56, 88, 104, 176, 304, 336, 400, 224, 352, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_233, vertices_961, vertices_94, vertices_838, vertices_340, vertices_916, vertices_376, vertices_432, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_193, vertices_577, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_176, vertices_304, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_233), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 6 7 8 916 148 3
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
cert_coverFacet 3 916
cert_cover_5 3 0 1 3 6 7 148 916 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coverFacet 6 480
cert_cover_2 6 5 4 6 7 224 480 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1271

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1273.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1273

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 361, 417, 961, 94, 838, 340, 916, 440, 344, 7, 11, 515, 53, 133, 41, 73, 161, 289, 321, 577, 385, 641, 30, 70, 518, 74, 578, 84, 148, 276, 324, 644, 772, 56, 88, 280, 296, 328, 176, 336, 400, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_417, vertices_961, vertices_94, vertices_838, vertices_340, vertices_916, vertices_440, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_417), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1273

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1274.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1274

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 587, 181, 425, 329, 961, 94, 838, 340, 916, 376, 432, 7, 11, 515, 53, 133, 41, 73, 265, 161, 321, 577, 385, 641, 30, 70, 518, 74, 578, 84, 148, 276, 324, 644, 772, 56, 88, 296, 328, 176, 304, 336, 400, 416, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_425, vertices_329, vertices_961, vertices_94, vertices_838, vertices_340, vertices_916, vertices_376, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_265, vertices_161, vertices_321, vertices_577, vertices_385, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_425), (false, vertices_329), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_304), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_329) then 0 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_329), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 1 3 6 7 8 916 148 3
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
cert_coverFacet 3 916
cert_cover_5 3 0 1 3 6 7 148 916 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1274

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1440 : Certifies 1440 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1233.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1441 : Certifies 1441 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1242.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1442 : Certifies 1442 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1243.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1443 : Certifies 1443 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1244.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1444 : Certifies 1444 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1245.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1445 : Certifies 1445 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1246.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1446 : Certifies 1446 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1247.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1447 : Certifies 1447 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1248.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1448 : Certifies 1448 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1249.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1449 : Certifies 1449 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1250.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1450 : Certifies 1450 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1251.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1451 : Certifies 1451 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1253.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1452 : Certifies 1452 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1254.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1453 : Certifies 1453 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1255.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1454 : Certifies 1454 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1256.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1455 : Certifies 1455 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1258.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1456 : Certifies 1456 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1260.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1457 : Certifies 1457 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1261.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1458 : Certifies 1458 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1262.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1459 : Certifies 1459 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1263.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1460 : Certifies 1460 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1264.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1461 : Certifies 1461 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1265.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1462 : Certifies 1462 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1266.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1463 : Certifies 1463 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1267.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1464 : Certifies 1464 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1268.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1465 : Certifies 1465 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1269.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1466 : Certifies 1466 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1270.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1467 : Certifies 1467 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1271.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1468 : Certifies 1468 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1273.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1469 : Certifies 1469 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1274.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B048 (j : Fin 30) :
    Certifies (1440 + j.val) := by
  fin_cases j
  · exact projection_1440
  · exact projection_1441
  · exact projection_1442
  · exact projection_1443
  · exact projection_1444
  · exact projection_1445
  · exact projection_1446
  · exact projection_1447
  · exact projection_1448
  · exact projection_1449
  · exact projection_1450
  · exact projection_1451
  · exact projection_1452
  · exact projection_1453
  · exact projection_1454
  · exact projection_1455
  · exact projection_1456
  · exact projection_1457
  · exact projection_1458
  · exact projection_1459
  · exact projection_1460
  · exact projection_1461
  · exact projection_1462
  · exact projection_1463
  · exact projection_1464
  · exact projection_1465
  · exact projection_1466
  · exact projection_1467
  · exact projection_1468
  · exact projection_1469

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
