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
/- Source: ProjectionCertificates/R_one_six_0134.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0134

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 899, 789, 233, 689, 78, 454, 92, 852, 632, 992, 7, 11, 131, 259, 21, 261, 41, 201, 49, 529, 161, 641, 769, 14, 70, 262, 74, 194, 386, 28, 76, 84, 788, 324, 56, 88, 104, 560, 592, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_899, vertices_789, vertices_233, vertices_689, vertices_78, vertices_454, vertices_92, vertices_852, vertices_632, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_41, vertices_201, vertices_49, vertices_529, vertices_161, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_194, vertices_386, vertices_28, vertices_76, vertices_84, vertices_788, vertices_324, vertices_56, vertices_88, vertices_104, vertices_560, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_899), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_70), (true, vertices_76), (true, vertices_84), (true, vertices_324), (true, vertices_88), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_899) then 11 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_233) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_2 1 1 3 7 8 788
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 7 84 852 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0134

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0135.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0135

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 451, 205, 905, 598, 794, 834, 236, 628, 696, 992, 7, 11, 67, 259, 13, 69, 137, 265, 193, 385, 22, 70, 26, 266, 530, 322, 578, 770, 44, 204, 52, 596, 100, 56, 536, 168, 648, 776, 560, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_451, vertices_205, vertices_905, vertices_598, vertices_794, vertices_834, vertices_236, vertices_628, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_137, vertices_265, vertices_193, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_204, vertices_52, vertices_596, vertices_100, vertices_56, vertices_536, vertices_168, vertices_648, vertices_776, vertices_560, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_451), (false, vertices_205), (false, vertices_905), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_596), (true, vertices_100), (true, vertices_536), (true, vertices_168), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_596) then 18 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 26 3
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_2 3 1 3 5 8 596
cert_row_2 4 1 2 5 6 204
cert_rows_2
cert_pivot 0 7 4 3 1
cert_heightProof 5
cert_coverFacet 0 598
cert_cover_5 0 3 0 1 3 5 22 598 3
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 26 794 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 236
cert_cover_5 3 4 1 2 4 5 44 236 3
cert_coverFacet 4 628
cert_cover_5 4 3 1 3 4 5 52 628 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0135

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0136.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0136

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 899, 789, 233, 689, 78, 454, 348, 376, 816, 992, 7, 11, 131, 259, 21, 261, 41, 201, 49, 529, 161, 641, 769, 14, 70, 262, 74, 194, 386, 28, 76, 276, 324, 56, 344, 104, 304, 560, 784, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_899, vertices_789, vertices_233, vertices_689, vertices_78, vertices_454, vertices_348, vertices_376, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_41, vertices_201, vertices_49, vertices_529, vertices_161, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_194, vertices_386, vertices_28, vertices_76, vertices_276, vertices_324, vertices_56, vertices_344, vertices_104, vertices_304, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_899), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_70), (true, vertices_76), (true, vertices_324), (true, vertices_344), (true, vertices_304), (true, vertices_352), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 16 13 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_899) then 9 else
  if p.val = (false, vertices_789) then 12 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_689) then 14 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_344) then 15 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 7 344
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 0 2 4
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 28 348 3
cert_coverFacet 3 376
cert_cover_5 3 0 2 3 4 5 56 376 3
cert_coverFacet 4 816
cert_cover_2 4 4 3 7 8 304 816 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0136

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0137.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0137

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 451, 341, 793, 206, 906, 236, 116, 696, 880, 992, 7, 11, 67, 259, 21, 69, 25, 265, 273, 321, 14, 70, 138, 266, 194, 386, 44, 204, 52, 84, 100, 56, 536, 168, 648, 776, 112, 560, 336, 784, 224, 864, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_451, vertices_341, vertices_793, vertices_206, vertices_906, vertices_236, vertices_116, vertices_696, vertices_880, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_273, vertices_321, vertices_14, vertices_70, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_204, vertices_52, vertices_84, vertices_100, vertices_56, vertices_536, vertices_168, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_864, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_451), (false, vertices_341), (false, vertices_793), (true, vertices_138), (true, vertices_204), (true, vertices_100), (true, vertices_168), (true, vertices_648), (true, vertices_112), (true, vertices_560), (true, vertices_224), (true, vertices_864), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_451) then 12 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_204) then 16 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_864) then 21 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(true, vertices_864), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_2 1 4 5 7 8 864
cert_row_4 2 0 2 6 7 8 906 138 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 906
cert_cover_5 1 2 0 2 6 7 138 906 3
cert_coverFacet 2 236
cert_cover_5 2 0 1 2 4 5 44 236 3
cert_coverFacet 3 116
cert_cover_2 3 3 1 4 5 52 116 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 56 696 3
cert_coverFacet 5 880
cert_cover_5 5 1 3 4 5 7 112 880 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0137

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0138.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0138

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 899, 533, 233, 689, 78, 454, 92, 852, 632, 992, 7, 11, 131, 771, 21, 517, 41, 201, 49, 529, 161, 641, 14, 70, 262, 74, 194, 386, 28, 76, 84, 532, 324, 772, 56, 88, 104, 560, 592, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_899, vertices_533, vertices_233, vertices_689, vertices_78, vertices_454, vertices_92, vertices_852, vertices_632, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_771, vertices_21, vertices_517, vertices_41, vertices_201, vertices_49, vertices_529, vertices_161, vertices_641, vertices_14, vertices_70, vertices_262, vertices_74, vertices_194, vertices_386, vertices_28, vertices_76, vertices_84, vertices_532, vertices_324, vertices_772, vertices_56, vertices_88, vertices_104, vertices_560, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_899), (false, vertices_533), (false, vertices_233), (false, vertices_689), (true, vertices_70), (true, vertices_76), (true, vertices_84), (true, vertices_324), (true, vertices_88), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 10 11 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_233) then 14 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
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
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 92
cert_cover_2 2 2 1 3 5 28 92 3
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 7 84 852 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0138

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0139.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0139

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 533, 837, 233, 625, 782, 454, 906, 540, 696, 992, 7, 11, 67, 21, 69, 517, 41, 201, 49, 529, 97, 577, 14, 70, 262, 138, 778, 194, 386, 28, 524, 532, 324, 772, 56, 536, 168, 648, 560, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_533, vertices_837, vertices_233, vertices_625, vertices_782, vertices_454, vertices_906, vertices_540, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_517, vertices_41, vertices_201, vertices_49, vertices_529, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_138, vertices_778, vertices_194, vertices_386, vertices_28, vertices_524, vertices_532, vertices_324, vertices_772, vertices_56, vertices_536, vertices_168, vertices_648, vertices_560, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_533), (false, vertices_837), (false, vertices_233), (false, vertices_625), (true, vertices_262), (true, vertices_778), (true, vertices_386), (true, vertices_524), (true, vertices_536), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 10 17 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_837) then 11 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_625) then 14 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_778) then 16 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 0 2 7 8 778
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 1 0 2 4
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
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0139

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0140.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0140

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 410, 556, 628, 184, 936, 752, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 84, 548, 580, 56, 152, 168, 552, 392, 776, 624, 176, 208, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_410, vertices_556, vertices_628, vertices_184, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_152, vertices_168, vertices_552, vertices_392, vertices_776, vertices_624, vertices_176, vertices_208, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_146), (true, vertices_84), (true, vertices_548), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_624), (true, vertices_176), (true, vertices_208), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 17 19 20 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_624) then 18 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 3 4 5 8 624
cert_row_4 2 0 2 3 6 7 410 26 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 26 410 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 52 628 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 936
cert_cover_5 5 3 2 4 6 7 168 936 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 6 624 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0140

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0141.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0141

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 410, 812, 692, 708, 312, 944, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 148, 548, 196, 580, 644, 56, 280, 296, 776, 688, 304, 400, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_410, vertices_812, vertices_692, vertices_708, vertices_312, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_148, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_296, vertices_776, vertices_688, vertices_304, vertices_400, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_146), (true, vertices_148), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_280), (true, vertices_296), (true, vertices_688), (true, vertices_304), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 17 19 20 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_688) then 18 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
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
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 944
cert_cover_5 6 2 3 4 6 7 688 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0141

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0142.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0142

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 410, 556, 436, 932, 708, 824, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 148, 420, 548, 196, 580, 644, 56, 280, 552, 776, 304, 400, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_410, vertices_556, vertices_436, vertices_932, vertices_708, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_148, vertices_420, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_146), (true, vertices_148), (true, vertices_420), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_280), (true, vertices_552), (true, vertices_304), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 18 19 20 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_420) then 16 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 1 4 6 7 420
cert_row_4 2 0 2 3 6 7 410 26 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 1 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 26 410 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 932
cert_cover_5 4 1 1 4 6 8 420 932 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0142

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0143.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0143

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 809, 689, 705, 782, 454, 962, 412, 440, 928, 7, 11, 67, 21, 69, 41, 521, 49, 145, 545, 193, 577, 641, 14, 70, 262, 522, 450, 578, 770, 28, 268, 148, 196, 388, 56, 408, 296, 776, 176, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_809, vertices_689, vertices_705, vertices_782, vertices_454, vertices_962, vertices_412, vertices_440, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_262, vertices_522, vertices_450, vertices_578, vertices_770, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_809), (false, vertices_689), (false, vertices_705), (true, vertices_262), (true, vertices_450), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_408), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 9 else
  if p.val = (false, vertices_213) then 13 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_450) then 10 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_408) then 16 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 1 2 7 8 782 14 3
cert_rows_3
cert_pivot_3 5 3 0
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 8 450 962 3
cert_coverFacet 3 412
cert_cover_5 3 0 1 2 3 6 28 412 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0143

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0144.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0144

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 410, 556, 180, 740, 824, 944, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 148, 164, 548, 196, 580, 56, 280, 552, 776, 176, 816, 400, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_410, vertices_556, vertices_180, vertices_740, vertices_824, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_56, vertices_280, vertices_552, vertices_776, vertices_176, vertices_816, vertices_400, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_146), (true, vertices_148), (true, vertices_164), (true, vertices_548), (true, vertices_196), (true, vertices_280), (true, vertices_552), (true, vertices_176), (true, vertices_816), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 17 19 20 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_2 1 3 4 7 8 816
cert_row_4 2 0 1 3 5 6 214 22 3
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 26 410 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 180
cert_cover_2 3 3 1 4 6 52 180 3
cert_coverFacet 4 740
cert_cover_5 4 3 1 4 5 6 164 740 2
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0144

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0145.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0145

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 597, 617, 689, 398, 454, 156, 724, 440, 360, 992, 7, 11, 67, 21, 69, 41, 73, 49, 529, 545, 577, 14, 70, 390, 266, 322, 28, 140, 596, 148, 196, 56, 152, 104, 296, 328, 392, 176, 656, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_597, vertices_617, vertices_689, vertices_398, vertices_454, vertices_156, vertices_724, vertices_440, vertices_360, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_73, vertices_49, vertices_529, vertices_545, vertices_577, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_104, vertices_296, vertices_328, vertices_392, vertices_176, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_597), (false, vertices_617), (false, vertices_689), (true, vertices_390), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_296), (true, vertices_392), (true, vertices_352), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (true, vertices_390) then 13 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 0 1 6 7 390
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 596 724 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 360
cert_cover_2 5 4 2 5 7 104 360 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0145

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0151.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0151

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 85, 809, 625, 961, 398, 454, 156, 724, 440, 944, 7, 11, 67, 21, 69, 41, 265, 49, 81, 545, 321, 577, 769, 14, 70, 390, 266, 322, 28, 140, 84, 148, 196, 56, 152, 296, 392, 432, 560, 592, 656, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_85, vertices_809, vertices_625, vertices_961, vertices_398, vertices_454, vertices_156, vertices_724, vertices_440, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_81, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_84, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_85), (false, vertices_809), (false, vertices_625), (false, vertices_961), (true, vertices_390), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_432), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 13 15 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 9 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_809) then 14 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_390) then 10 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_432) then 17 else
  if p.val = (true, vertices_656) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 5 6 8 724 84 3
cert_rows_3
cert_pivot_3 4 0 1
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 944
cert_cover_5 5 1 3 4 6 8 432 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0151

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0152.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0152

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 85, 425, 817, 849, 398, 454, 156, 724, 696, 992, 7, 11, 67, 21, 69, 41, 265, 49, 81, 785, 289, 321, 14, 70, 390, 266, 322, 28, 140, 84, 148, 196, 56, 152, 168, 392, 560, 592, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_85, vertices_425, vertices_817, vertices_849, vertices_398, vertices_454, vertices_156, vertices_724, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_81, vertices_785, vertices_289, vertices_321, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_84, vertices_148, vertices_196, vertices_56, vertices_152, vertices_168, vertices_392, vertices_560, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_85), (false, vertices_425), (false, vertices_817), (false, vertices_849), (true, vertices_390), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_425) then 16 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_390) then 12 else
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
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0152

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0153.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0153

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 597, 809, 689, 833, 398, 454, 156, 724, 440, 992, 7, 11, 67, 21, 69, 41, 265, 49, 529, 545, 321, 577, 769, 14, 70, 390, 266, 322, 28, 140, 596, 148, 196, 56, 152, 296, 392, 176, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_597, vertices_809, vertices_689, vertices_833, vertices_398, vertices_454, vertices_156, vertices_724, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_176, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_597), (false, vertices_809), (false, vertices_689), (false, vertices_833), (true, vertices_390), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_390) then 12 else
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
cert_nodeAtPriority_3 833 140 148 196 152 392 416 448 704 331 390 597 809 689
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0153

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0154.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0154

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 597, 425, 817, 833, 398, 454, 156, 724, 696, 992, 7, 11, 67, 21, 69, 41, 265, 49, 529, 289, 321, 577, 769, 14, 70, 390, 266, 322, 28, 140, 596, 148, 196, 56, 152, 168, 392, 560, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_597, vertices_425, vertices_817, vertices_833, vertices_398, vertices_454, vertices_156, vertices_724, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_168, vertices_392, vertices_560, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_597), (false, vertices_425), (false, vertices_817), (false, vertices_833), (true, vertices_390), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_390) then 12 else
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
cert_nodeAtPriority_3 833 140 148 196 152 656 672 448 704 331 390 597 425 817
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0154

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0155.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0155

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 451, 597, 665, 705, 334, 300, 692, 868, 440, 992, 7, 11, 67, 387, 21, 69, 25, 137, 529, 193, 577, 641, 14, 70, 266, 322, 44, 268, 52, 532, 292, 548, 324, 580, 56, 152, 296, 392, 176, 656, 864, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_451, vertices_597, vertices_665, vertices_705, vertices_334, vertices_300, vertices_692, vertices_868, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_387, vertices_21, vertices_69, vertices_25, vertices_137, vertices_529, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_56, vertices_152, vertices_296, vertices_392, vertices_176, vertices_656, vertices_864, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_451), (false, vertices_597), (false, vertices_665), (false, vertices_705), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_296), (true, vertices_176), (true, vertices_864), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 11 else
  if p.val = (false, vertices_451) then 12 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_665) then 17 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_864) then 20 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(true, vertices_864), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_2 1 4 5 7 8 864
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 300
cert_cover_2 1 2 1 4 7 44 300 3
cert_coverFacet 2 692
cert_cover_5 2 2 1 3 4 6 52 692 3
cert_coverFacet 3 868
cert_cover_5 3 1 1 4 5 7 292 868 2
cert_coverFacet 4 440
cert_cover_5 4 3 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 7 864 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0155

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0156.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0156

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 597, 425, 369, 398, 454, 668, 708, 696, 624, 992, 7, 11, 67, 21, 69, 41, 265, 49, 81, 289, 321, 14, 70, 390, 266, 322, 28, 140, 532, 196, 580, 644, 56, 664, 168, 392, 112, 560, 592, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_597, vertices_425, vertices_369, vertices_398, vertices_454, vertices_668, vertices_708, vertices_696, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_81, vertices_289, vertices_321, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_664, vertices_168, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_597), (false, vertices_425), (false, vertices_369), (true, vertices_390), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_664), (true, vertices_560), (true, vertices_608), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 10 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_425) then 16 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_664) then 17 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 8 664
cert_row_2 1 0 1 6 7 390
cert_row_4 2 4 5 6 7 8 992 352 2
cert_rows_3
cert_pivot_3 0 2 4
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 0 1 2 3 6 28 668 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 696
cert_cover_5 4 0 2 3 4 6 56 696 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0156

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0157.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0157

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 597, 425, 817, 833, 398, 454, 668, 708, 696, 992, 7, 11, 67, 21, 69, 41, 265, 49, 529, 289, 321, 577, 769, 14, 70, 390, 266, 322, 28, 140, 532, 196, 580, 644, 56, 664, 168, 392, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_597, vertices_425, vertices_817, vertices_833, vertices_398, vertices_454, vertices_668, vertices_708, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_664, vertices_168, vertices_392, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_597), (false, vertices_425), (false, vertices_817), (false, vertices_833), (true, vertices_390), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_664), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 9 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_425) then 15 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_390) then 10 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_664) then 16 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_704) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
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
cert_coverFacet 2 668
cert_cover_5 2 0 1 2 3 6 28 668 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 696
cert_cover_5 4 0 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0157

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0158.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0158

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 213, 361, 625, 398, 454, 668, 824, 904, 720, 992, 7, 11, 67, 21, 69, 41, 329, 49, 81, 97, 14, 70, 390, 266, 322, 28, 140, 148, 196, 56, 536, 296, 392, 648, 776, 560, 208, 592, 656, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_213, vertices_361, vertices_625, vertices_398, vertices_454, vertices_668, vertices_824, vertices_904, vertices_720, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_329, vertices_49, vertices_81, vertices_97, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_148, vertices_196, vertices_56, vertices_536, vertices_296, vertices_392, vertices_648, vertices_776, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_213), (false, vertices_361), (false, vertices_625), (true, vertices_390), (true, vertices_140), (true, vertices_536), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_656), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (true, vertices_390) then 12 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_392) then 3 else
  if p.val = (true, vertices_648) then 4 else
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
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
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
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 3 6 8 668 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 904
cert_cover_2 4 6 2 7 8 392 904 3
cert_coverFacet 5 720
cert_cover_2 5 5 3 6 8 208 720 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0158

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0159.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0159

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 213, 361, 689, 225, 398, 454, 668, 824, 904, 992, 7, 11, 67, 21, 69, 41, 329, 49, 145, 97, 161, 193, 14, 70, 390, 266, 322, 28, 140, 148, 196, 56, 536, 296, 392, 648, 776, 560, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_213, vertices_361, vertices_689, vertices_225, vertices_398, vertices_454, vertices_668, vertices_824, vertices_904, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_329, vertices_49, vertices_145, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_148, vertices_196, vertices_56, vertices_536, vertices_296, vertices_392, vertices_648, vertices_776, vertices_560, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_213), (false, vertices_361), (false, vertices_689), (false, vertices_225), (true, vertices_390), (true, vertices_140), (true, vertices_536), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_213) then 14 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
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
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 3 6 8 668 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 904
cert_cover_2 4 6 2 7 8 392 904 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0159

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0160.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0160

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 597, 361, 689, 609, 398, 454, 668, 708, 440, 992, 7, 11, 67, 21, 69, 41, 329, 49, 529, 97, 545, 577, 14, 70, 390, 266, 322, 28, 140, 532, 196, 580, 644, 56, 152, 296, 392, 176, 656, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_597, vertices_361, vertices_689, vertices_609, vertices_398, vertices_454, vertices_668, vertices_708, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_329, vertices_49, vertices_529, vertices_97, vertices_545, vertices_577, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_152, vertices_296, vertices_392, vertices_176, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_597), (false, vertices_361), (false, vertices_689), (false, vertices_609), (true, vertices_390), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_152), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
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
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 3 6 8 668 28 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0160

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0161.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0161

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 533, 709, 361, 625, 398, 454, 668, 440, 688, 992, 7, 11, 67, 21, 69, 517, 41, 329, 49, 529, 97, 577, 14, 70, 390, 266, 322, 28, 140, 532, 196, 644, 56, 152, 296, 392, 176, 560, 656, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_533, vertices_709, vertices_361, vertices_625, vertices_398, vertices_454, vertices_668, vertices_440, vertices_688, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_517, vertices_41, vertices_329, vertices_49, vertices_529, vertices_97, vertices_577, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_532, vertices_196, vertices_644, vertices_56, vertices_152, vertices_296, vertices_392, vertices_176, vertices_560, vertices_656, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_533), (false, vertices_709), (false, vertices_361), (false, vertices_625), (true, vertices_390), (true, vertices_140), (true, vertices_152), (true, vertices_392), (true, vertices_176), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_709) then 14 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 3 6 8 668 28 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 440
cert_cover_5 3 2 2 3 4 6 56 440 3
cert_coverFacet 4 688
cert_cover_2 4 4 3 6 8 176 688 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0161

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0162.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0162

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 533, 709, 361, 625, 398, 454, 668, 440, 368, 976, 7, 11, 67, 21, 69, 517, 41, 329, 49, 529, 97, 577, 14, 70, 390, 266, 322, 28, 140, 532, 196, 644, 56, 152, 296, 392, 112, 304, 336, 592, 400, 656, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_533, vertices_709, vertices_361, vertices_625, vertices_398, vertices_454, vertices_668, vertices_440, vertices_368, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_517, vertices_41, vertices_329, vertices_49, vertices_529, vertices_97, vertices_577, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_532, vertices_196, vertices_644, vertices_56, vertices_152, vertices_296, vertices_392, vertices_112, vertices_304, vertices_336, vertices_592, vertices_400, vertices_656, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_533), (false, vertices_709), (false, vertices_361), (false, vertices_625), (true, vertices_390), (true, vertices_140), (true, vertices_152), (true, vertices_392), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_709) then 14 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 3 6 8 668 28 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 440
cert_cover_5 3 2 2 3 4 6 56 440 3
cert_coverFacet 4 368
cert_cover_2 4 4 3 5 7 112 368 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 336 976 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0162

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0163.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0163

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 533, 709, 361, 625, 398, 454, 668, 824, 904, 992, 7, 11, 67, 21, 69, 517, 41, 329, 49, 529, 97, 577, 14, 70, 390, 266, 322, 28, 140, 532, 196, 644, 56, 536, 296, 392, 648, 776, 560, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_533, vertices_709, vertices_361, vertices_625, vertices_398, vertices_454, vertices_668, vertices_824, vertices_904, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_517, vertices_41, vertices_329, vertices_49, vertices_529, vertices_97, vertices_577, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_392, vertices_648, vertices_776, vertices_560, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_533), (false, vertices_709), (false, vertices_361), (false, vertices_625), (true, vertices_390), (true, vertices_140), (true, vertices_536), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_709) then 14 else
  if p.val = (false, vertices_361) then 17 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 3 6 8 668 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 904
cert_cover_2 4 6 2 7 8 392 904 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0163

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0164.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0164

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 85, 425, 625, 929, 398, 454, 220, 696, 976, 7, 11, 67, 259, 21, 69, 41, 265, 49, 81, 417, 545, 577, 769, 14, 70, 390, 266, 322, 28, 140, 84, 196, 56, 152, 168, 392, 560, 208, 592, 656, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_85, vertices_425, vertices_625, vertices_929, vertices_398, vertices_454, vertices_220, vertices_696, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_81, vertices_417, vertices_545, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_152, vertices_168, vertices_392, vertices_560, vertices_208, vertices_592, vertices_656, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_85), (false, vertices_425), (false, vertices_625), (false, vertices_929), (true, vertices_390), (true, vertices_140), (true, vertices_196), (true, vertices_152), (true, vertices_208), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 14 15 17 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 10 else
  if p.val = (false, vertices_85) then 2 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_929) then 19 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 3 5 6 220 28 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 28 220 3
cert_coverFacet 3 696
cert_cover_5 3 2 2 3 4 6 56 696 3
cert_coverFacet 4 976
cert_cover_5 4 3 3 5 6 7 208 976 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0164

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0165.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0165

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 85, 809, 689, 721, 398, 454, 220, 440, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 81, 657, 545, 577, 769, 14, 70, 390, 266, 322, 28, 140, 84, 196, 56, 152, 296, 392, 176, 208, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_85, vertices_809, vertices_689, vertices_721, vertices_398, vertices_454, vertices_220, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_81, vertices_657, vertices_545, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_176, vertices_208, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_85), (false, vertices_809), (false, vertices_689), (false, vertices_721), (true, vertices_390), (true, vertices_140), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 14 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 10 else
  if p.val = (false, vertices_85) then 2 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_689) then 17 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
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
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 28 220 3
cert_coverFacet 3 440
cert_cover_5 3 2 2 3 4 6 56 440 3
cert_coverFacet 4 992
cert_cover_5 4 3 4 5 6 7 416 992 1
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0165

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0166.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0166

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 425, 817, 398, 454, 220, 248, 624, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 390, 266, 322, 28, 140, 84, 196, 56, 216, 168, 392, 112, 560, 592, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_425, vertices_817, vertices_398, vertices_454, vertices_220, vertices_248, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_216, vertices_168, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_390), (true, vertices_140), (true, vertices_196), (true, vertices_216), (true, vertices_112), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 9 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_425) then 15 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_390) then 10 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_216) then 16 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_448) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
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
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 28 220 3
cert_coverFacet 3 248
cert_cover_5 3 0 2 3 4 5 56 248 3
cert_coverFacet 4 624
cert_cover_2 4 4 3 5 8 112 624 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0166

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0167.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0167

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 425, 817, 398, 454, 668, 708, 696, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 390, 266, 322, 28, 140, 532, 196, 580, 644, 56, 664, 168, 392, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_425, vertices_817, vertices_398, vertices_454, vertices_668, vertices_708, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_664, vertices_168, vertices_392, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_390), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_664), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 9 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_425) then 15 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_390) then 10 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_664) then 16 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_704) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
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
cert_coverFacet 2 668
cert_cover_5 2 0 1 2 3 6 28 668 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 696
cert_cover_5 4 0 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0167

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0168.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0168

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 809, 689, 398, 454, 156, 724, 440, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 545, 577, 769, 14, 70, 390, 266, 322, 28, 140, 596, 148, 196, 56, 152, 296, 392, 176, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_809, vertices_689, vertices_398, vertices_454, vertices_156, vertices_724, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_176, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_809), (false, vertices_689), (true, vertices_390), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
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
  if p.val = (true, vertices_390) then 12 else
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
cert_nodeAtPriority_3 267 140 148 196 152 392 416 448 704 835 390 597 809 689
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0168

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0780 : Certifies 780 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0134.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0781 : Certifies 781 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0135.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0782 : Certifies 782 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0136.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0783 : Certifies 783 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0137.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0784 : Certifies 784 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0138.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0785 : Certifies 785 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0139.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0786 : Certifies 786 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0140.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0787 : Certifies 787 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0141.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0788 : Certifies 788 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0142.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0789 : Certifies 789 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0143.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0790 : Certifies 790 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0144.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0791 : Certifies 791 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0145.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0792 : Certifies 792 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0151.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0793 : Certifies 793 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0152.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0794 : Certifies 794 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0153.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0795 : Certifies 795 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0154.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0796 : Certifies 796 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0155.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0797 : Certifies 797 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0156.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0798 : Certifies 798 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0157.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0799 : Certifies 799 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0158.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0800 : Certifies 800 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0159.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0801 : Certifies 801 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0160.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0802 : Certifies 802 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0161.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0803 : Certifies 803 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0162.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0804 : Certifies 804 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0163.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0805 : Certifies 805 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0164.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0806 : Certifies 806 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0165.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0807 : Certifies 807 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0166.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0808 : Certifies 808 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0167.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0809 : Certifies 809 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0168.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B026 (j : Fin 30) :
    Certifies (780 + j.val) := by
  fin_cases j
  · exact projection_0780
  · exact projection_0781
  · exact projection_0782
  · exact projection_0783
  · exact projection_0784
  · exact projection_0785
  · exact projection_0786
  · exact projection_0787
  · exact projection_0788
  · exact projection_0789
  · exact projection_0790
  · exact projection_0791
  · exact projection_0792
  · exact projection_0793
  · exact projection_0794
  · exact projection_0795
  · exact projection_0796
  · exact projection_0797
  · exact projection_0798
  · exact projection_0799
  · exact projection_0800
  · exact projection_0801
  · exact projection_0802
  · exact projection_0803
  · exact projection_0804
  · exact projection_0805
  · exact projection_0806
  · exact projection_0807
  · exact projection_0808
  · exact projection_0809

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
