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
/- Source: ProjectionCertificates/R_one_six_0865.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0865

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 790, 122, 850, 812, 564, 744, 904, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 786, 322, 44, 268, 52, 532, 548, 772, 104, 552, 200, 392, 648, 776, 112, 560, 592, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_790, vertices_122, vertices_850, vertices_812, vertices_564, vertices_744, vertices_904, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_786, vertices_322, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 18 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 1 82 0 532 548 772 104 552 648 776 112 560 592 608 327 397 203 786
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 7 8 812 44 3
cert_row_2 1 0 3 7 8 786
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 22 790 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 82 850 3
cert_coverFacet 3 812
cert_cover_5 3 0 1 2 4 7 44 812 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0865

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0866.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0866

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 278, 122, 338, 172, 692, 916, 744, 880, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 140, 52, 660, 276, 164, 388, 104, 168, 200, 112, 560, 336, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_338, vertices_172, vertices_692, vertices_916, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_660, vertices_276, vertices_164, vertices_388, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_660), (true, vertices_276), (true, vertices_164), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
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
cert_nodeAtPriority_20 0 82 1 274 276 164 104 168 112 560 336 784 608 672 327 203 397 660
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_2 1 1 3 6 8 660
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 916
cert_cover_5 5 1 1 3 6 7 660 916 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 104 744 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0866

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0867.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0867

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 278, 122, 338, 684, 564, 916, 744, 880, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 140, 52, 276, 532, 548, 388, 644, 104, 680, 200, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_338, vertices_684, vertices_564, vertices_916, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_532, vertices_548, vertices_388, vertices_644, vertices_104, vertices_680, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_104), (true, vertices_680), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
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
cert_nodeAtPriority_26 82 274 276 532 548 644 104 112 560 336 784 608 327 203 397 680
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_2 1 2 4 6 8 680
cert_row_4 2 1 3 6 7 8 916 276 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 916
cert_cover_5 5 2 1 3 6 7 276 916 2
cert_coverFacet 6 744
cert_cover_5 6 1 2 4 5 6 104 744 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0867

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0868.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0868

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 790, 122, 338, 684, 564, 900, 744, 880, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 140, 52, 532, 548, 388, 644, 772, 104, 680, 200, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_790, vertices_122, vertices_338, vertices_684, vertices_564, vertices_900, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_532, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_680, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_680), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
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
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_680) then 19 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
cert_nodeAtPriority_26 82 274 532 548 644 772 104 112 560 336 784 608 327 203 397 680
cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 8 680
cert_row_2 1 0 2 3 4 58
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 6 2 0 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 22 790 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 744
cert_cover_5 6 0 2 4 5 6 104 744 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0868

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0869.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0869

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 278, 122, 850, 172, 820, 932, 232, 752, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 140, 52, 276, 164, 804, 388, 104, 168, 200, 112, 560, 592, 784, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_850, vertices_172, vertices_820, vertices_932, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_164, vertices_804, vertices_388, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_276), (true, vertices_164), (true, vertices_804), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
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
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_804) then 18 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 82 1 274 276 164 104 168 112 560 592 784 224 672 327 203 397 804
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 7 8 804
cert_row_2 1 0 2 3 4 58
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 932
cert_cover_5 5 0 1 4 6 7 164 932 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0869

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0870.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0870

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 278, 122, 850, 172, 692, 916, 744, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 140, 52, 660, 276, 164, 388, 104, 168, 200, 112, 560, 592, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_850, vertices_172, vertices_692, vertices_916, vertices_744, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_660, vertices_276, vertices_164, vertices_388, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_660), (true, vertices_276), (true, vertices_164), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
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
  if p.val = (true, vertices_660) then 18 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 82 1 274 276 164 104 168 112 560 592 784 608 672 327 203 397 660
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 6 8 660
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
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 692
cert_cover_5 4 0 1 3 4 6 52 692 3
cert_coverFacet 5 916
cert_cover_5 5 0 1 3 6 7 660 916 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0870

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0871.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0871

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 278, 122, 850, 172, 820, 932, 744, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 140, 52, 276, 164, 804, 388, 104, 168, 200, 112, 560, 592, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_850, vertices_172, vertices_820, vertices_932, vertices_744, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_164, vertices_804, vertices_388, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_276), (true, vertices_164), (true, vertices_804), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
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
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_804) then 18 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 82 1 274 276 164 104 168 112 560 592 784 608 672 327 203 397 804
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
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 932
cert_cover_5 5 0 1 4 6 7 164 932 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0871

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0872.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0872

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 398, 962, 172, 436, 744, 624, 944, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 194, 322, 386, 44, 140, 52, 276, 164, 388, 104, 168, 200, 112, 432, 560, 592, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_398, vertices_962, vertices_172, vertices_436, vertices_744, vertices_624, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_52, vertices_276, vertices_164, vertices_388, vertices_104, vertices_168, vertices_200, vertices_112, vertices_432, vertices_560, vertices_592, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_386), (true, vertices_140), (true, vertices_164), (true, vertices_388), (true, vertices_168), (true, vertices_432), (true, vertices_560), (true, vertices_608), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 15 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_432) then 20 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 194 962 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 436
cert_cover_5 3 0 1 3 4 6 52 436 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0872

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0873.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0873

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 278, 122, 850, 684, 820, 900, 744, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 140, 52, 276, 548, 388, 644, 772, 104, 680, 200, 112, 560, 592, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_850, vertices_684, vertices_820, vertices_900, vertices_744, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_680, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_276), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_680), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
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
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_680) then 19 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
cert_nodeAtPriority_26 82 274 276 548 644 772 104 112 560 592 784 608 327 203 397 680
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
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 744
cert_cover_5 6 0 2 4 5 6 104 744 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0873

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0874.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0874

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 278, 122, 850, 684, 564, 916, 744, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 274, 322, 44, 140, 52, 276, 532, 548, 388, 644, 104, 680, 200, 112, 560, 592, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_850, vertices_684, vertices_564, vertices_916, vertices_744, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_532, vertices_548, vertices_388, vertices_644, vertices_104, vertices_680, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_104), (true, vertices_680), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
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
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_680) then 19 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
cert_nodeAtPriority_26 82 274 276 532 548 644 104 112 560 592 784 608 327 203 397 680
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_2 1 0 2 3 4 58
cert_row_2 2 2 4 6 8 680
cert_row_4 3 1 3 6 7 8 916 276 2
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 916
cert_cover_5 5 3 1 3 6 7 276 916 2
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 104 744 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0874

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0875.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0875

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 790, 122, 850, 684, 564, 900, 232, 752, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 786, 322, 44, 140, 52, 532, 548, 388, 644, 772, 104, 168, 200, 112, 560, 592, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_790, vertices_122, vertices_850, vertices_684, vertices_564, vertices_900, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_786, vertices_322, vertices_44, vertices_140, vertices_52, vertices_532, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 18 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 1 82 0 532 548 644 772 104 168 112 560 592 224 672 327 397 203 786
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 7 8 786
cert_row_2 1 0 2 3 4 58
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 0 1 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0875

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0876.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0876

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 790, 122, 850, 172, 692, 900, 744, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 786, 322, 44, 140, 52, 532, 164, 388, 644, 772, 104, 168, 200, 112, 560, 592, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_790, vertices_122, vertices_850, vertices_172, vertices_692, vertices_900, vertices_744, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_786, vertices_322, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 18 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 1 82 0 532 164 644 772 104 168 112 560 592 608 672 327 397 203 786
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 7 8 786
cert_row_2 1 0 2 3 4 58
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0876

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0877.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0877

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 790, 122, 850, 172, 564, 932, 232, 752, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 786, 322, 44, 140, 52, 532, 164, 548, 388, 772, 104, 168, 200, 112, 560, 592, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_790, vertices_122, vertices_850, vertices_172, vertices_564, vertices_932, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_786, vertices_322, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_548, vertices_388, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 18 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 1 82 0 532 164 548 772 104 168 112 560 592 224 672 327 397 203 786
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_2 1 0 3 7 8 786
cert_row_4 2 1 4 6 7 8 932 164 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 22 790 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 932
cert_cover_5 5 2 1 4 6 7 164 932 3
cert_coverFacet 6 232
cert_cover_2 6 4 2 5 6 104 232 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0877

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0878.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0878

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 397, 961, 790, 122, 850, 172, 564, 932, 744, 624, 7, 11, 67, 13, 261, 137, 193, 321, 385, 22, 262, 58, 74, 82, 786, 322, 44, 140, 52, 532, 164, 548, 388, 772, 104, 168, 200, 112, 560, 592, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_790, vertices_122, vertices_850, vertices_172, vertices_564, vertices_932, vertices_744, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_786, vertices_322, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_548, vertices_388, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 18 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 1 82 0 532 164 548 772 104 168 112 560 592 608 672 327 397 203 786
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 6 7 8 932 164 3
cert_row_2 1 0 3 7 8 786
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 22 790 3
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 932
cert_cover_5 5 0 1 4 6 7 164 932 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0878

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0879.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0879

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 398, 962, 428, 820, 232, 752, 928, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 194, 322, 386, 44, 396, 52, 276, 292, 104, 168, 200, 112, 560, 592, 784, 224, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_398, vertices_962, vertices_428, vertices_820, vertices_232, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_276, vertices_292, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_386), (true, vertices_396), (true, vertices_292), (true, vertices_168), (true, vertices_560), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
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
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0879

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0880.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0880

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 398, 962, 428, 820, 744, 624, 928, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 194, 322, 386, 44, 396, 52, 276, 292, 104, 168, 200, 112, 560, 592, 784, 608, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_398, vertices_962, vertices_428, vertices_820, vertices_744, vertices_624, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_276, vertices_292, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_608, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_386), (true, vertices_396), (true, vertices_292), (true, vertices_168), (true, vertices_560), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
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
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0880

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0881.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0881

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 398, 962, 428, 308, 744, 624, 944, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 194, 322, 386, 44, 396, 52, 276, 292, 104, 168, 200, 112, 304, 560, 592, 784, 608, 416, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_398, vertices_962, vertices_428, vertices_308, vertices_744, vertices_624, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_276, vertices_292, vertices_104, vertices_168, vertices_200, vertices_112, vertices_304, vertices_560, vertices_592, vertices_784, vertices_608, vertices_416, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_386), (true, vertices_396), (true, vertices_292), (true, vertices_168), (true, vertices_304), (true, vertices_560), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 428
cert_cover_5 2 0 1 2 4 6 44 428 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0881

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0882.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0882

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 789, 121, 337, 398, 962, 556, 908, 564, 744, 880, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 194, 322, 386, 44, 396, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_789, vertices_121, vertices_337, vertices_398, vertices_962, vertices_556, vertices_908, vertices_564, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_337), (true, vertices_386), (true, vertices_396), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_608), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_396) then 16 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 908
cert_cover_5 3 0 1 2 6 8 396 908 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0882

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0883.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0883

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 398, 962, 556, 908, 820, 744, 624, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 138, 194, 322, 386, 44, 396, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 560, 592, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_398, vertices_962, vertices_556, vertices_908, vertices_820, vertices_744, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_592, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_386), (true, vertices_396), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
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
cert_row_2 2 1 2 6 7 396
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 14 398 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 908
cert_cover_5 3 2 1 2 6 8 396 908 3
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 52 820 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0883

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0884.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0884

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 654, 774, 962, 684, 820, 232, 752, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 262, 518, 138, 194, 322, 642, 770, 44, 652, 52, 276, 548, 772, 104, 168, 200, 112, 560, 592, 784, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_654, vertices_774, vertices_962, vertices_684, vertices_820, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_262, vertices_518, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_518), (true, vertices_642), (true, vertices_770), (true, vertices_652), (true, vertices_548), (true, vertices_772), (true, vertices_168), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_652) then 15 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
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
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0884

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0885.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0885

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 781, 649, 961, 790, 122, 850, 684, 564, 232, 752, 7, 11, 67, 13, 261, 137, 521, 193, 321, 641, 769, 22, 262, 58, 74, 82, 786, 322, 44, 524, 52, 532, 548, 772, 104, 168, 200, 648, 112, 560, 592, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_781, vertices_649, vertices_961, vertices_790, vertices_122, vertices_850, vertices_684, vertices_564, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_786, vertices_322, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_781), (false, vertices_649), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_532), (true, vertices_548), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_781) then 13 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_786) then 17 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row_2 0 0 3 7 8 786
cert_row_2 1 0 2 3 4 58
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 0 1 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0885

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0886.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0886

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 789, 121, 337, 142, 902, 962, 172, 692, 744, 880, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 134, 262, 138, 194, 322, 898, 44, 140, 52, 532, 164, 644, 772, 104, 168, 200, 112, 560, 336, 784, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_789, vertices_121, vertices_337, vertices_142, vertices_902, vertices_962, vertices_172, vertices_692, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_134, vertices_262, vertices_138, vertices_194, vertices_322, vertices_898, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_337), (true, vertices_134), (true, vertices_898), (true, vertices_140), (true, vertices_164), (true, vertices_644), (true, vertices_168), (true, vertices_560), (true, vertices_608), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_898) then 16 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
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
cert_row_2 0 0 6 7 8 898
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0886

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0887.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0887

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 203, 277, 121, 849, 142, 902, 962, 684, 820, 232, 752, 7, 11, 67, 21, 261, 57, 73, 81, 273, 321, 14, 134, 262, 138, 194, 322, 898, 44, 140, 52, 276, 548, 644, 772, 104, 168, 200, 112, 560, 592, 784, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_277, vertices_121, vertices_849, vertices_142, vertices_902, vertices_962, vertices_684, vertices_820, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_321, vertices_14, vertices_134, vertices_262, vertices_138, vertices_194, vertices_322, vertices_898, vertices_44, vertices_140, vertices_52, vertices_276, vertices_548, vertices_644, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (true, vertices_134), (true, vertices_898), (true, vertices_140), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_168), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 11 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_898) then 15 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 6 7 8 898
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0887

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0888.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0888

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 297, 225, 929, 334, 962, 348, 824, 752, 848, 7, 11, 131, 53, 69, 41, 265, 97, 161, 289, 193, 385, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 280, 296, 112, 560, 336, 592, 784, 224, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_297, vertices_225, vertices_929, vertices_334, vertices_962, vertices_348, vertices_824, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_161, vertices_289, vertices_193, vertices_385, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_296, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_297), (false, vertices_225), (false, vertices_929), (true, vertices_322), (true, vertices_332), (true, vertices_280), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_332) then 16 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
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
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 28 348 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 752
cert_cover_5 4 3 3 4 5 6 112 752 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0888

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0889.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0889

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 395, 341, 681, 817, 897, 206, 962, 124, 232, 752, 848, 7, 11, 259, 21, 325, 41, 137, 49, 273, 545, 385, 641, 769, 14, 70, 138, 194, 322, 386, 60, 76, 84, 104, 168, 200, 112, 560, 336, 592, 784, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_395, vertices_341, vertices_681, vertices_817, vertices_897, vertices_206, vertices_962, vertices_124, vertices_232, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_325, vertices_41, vertices_137, vertices_49, vertices_273, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_322, vertices_386, vertices_60, vertices_76, vertices_84, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_395), (false, vertices_341), (false, vertices_681), (false, vertices_817), (false, vertices_897), (true, vertices_194), (true, vertices_76), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_592), (true, vertices_224), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_395) then 11 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 5 60 124 3
cert_coverFacet 3 232
cert_cover_2 3 4 2 5 6 104 232 3
cert_coverFacet 4 752
cert_cover_5 4 3 3 4 5 6 112 752 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0889

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0890.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0890

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 681, 609, 705, 334, 962, 348, 440, 880, 928, 7, 11, 131, 53, 69, 41, 137, 97, 545, 193, 577, 641, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 280, 168, 392, 112, 304, 336, 608, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_681, vertices_609, vertices_705, vertices_334, vertices_962, vertices_348, vertices_440, vertices_880, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_168, vertices_392, vertices_112, vertices_304, vertices_336, vertices_608, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_681), (false, vertices_609), (false, vertices_705), (true, vertices_322), (true, vertices_332), (true, vertices_280), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_332) then 16 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 6 7 440 56 3
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
cert_coverFacet 3 440
cert_cover_5 3 2 2 3 4 6 56 440 3
cert_coverFacet 4 880
cert_cover_5 4 3 3 4 5 7 112 880 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0890

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0891.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0891

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 681, 609, 705, 334, 962, 348, 568, 920, 880, 7, 11, 131, 53, 69, 41, 137, 97, 545, 193, 577, 641, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 280, 536, 552, 392, 648, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_681, vertices_609, vertices_705, vertices_334, vertices_962, vertices_348, vertices_568, vertices_920, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_536, vertices_552, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_681), (false, vertices_609), (false, vertices_705), (true, vertices_322), (true, vertices_332), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_332) then 16 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0891

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0892.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0892

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 681, 225, 334, 962, 348, 568, 920, 880, 736, 7, 11, 131, 53, 69, 41, 137, 97, 161, 193, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 280, 536, 552, 392, 648, 112, 560, 336, 784, 224, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_681, vertices_225, vertices_334, vertices_962, vertices_348, vertices_568, vertices_920, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_536, vertices_552, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_681), (false, vertices_225), (true, vertices_322), (true, vertices_332), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_608), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_332) then 17 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
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
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0892

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0893.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0893

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 169, 737, 334, 962, 348, 568, 920, 680, 880, 7, 11, 131, 53, 69, 41, 137, 97, 161, 193, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 280, 536, 168, 552, 392, 648, 112, 560, 336, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_169, vertices_737, vertices_334, vertices_962, vertices_348, vertices_568, vertices_920, vertices_680, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_169), (false, vertices_737), (true, vertices_322), (true, vertices_332), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_332) then 17 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
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
  | 17 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0893

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0894.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0894

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 169, 737, 334, 962, 348, 184, 920, 880, 688, 7, 11, 131, 53, 69, 41, 137, 97, 161, 193, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 152, 280, 168, 392, 112, 176, 560, 336, 656, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_169, vertices_737, vertices_334, vertices_962, vertices_348, vertices_184, vertices_920, vertices_880, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_152, vertices_280, vertices_168, vertices_392, vertices_112, vertices_176, vertices_560, vertices_336, vertices_656, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_169), (false, vertices_737), (true, vertices_322), (true, vertices_332), (true, vertices_152), (true, vertices_280), (true, vertices_176), (true, vertices_560), (true, vertices_336), (true, vertices_656), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_332) then 17 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 6 7 8 920 152 3
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
cert_coverFacet 3 184
cert_cover_2 3 3 2 4 6 56 184 3
cert_coverFacet 4 920
cert_cover_5 4 2 2 3 6 7 152 920 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coverFacet 6 688
cert_cover_2 6 4 3 6 8 176 688 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0894

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1200 : Certifies 1200 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0865.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1201 : Certifies 1201 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0866.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1202 : Certifies 1202 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0867.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1203 : Certifies 1203 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0868.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1204 : Certifies 1204 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0869.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1205 : Certifies 1205 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0870.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1206 : Certifies 1206 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0871.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1207 : Certifies 1207 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0872.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1208 : Certifies 1208 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0873.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1209 : Certifies 1209 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0874.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1210 : Certifies 1210 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0875.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1211 : Certifies 1211 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0876.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1212 : Certifies 1212 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0877.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1213 : Certifies 1213 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0878.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1214 : Certifies 1214 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0879.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1215 : Certifies 1215 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0880.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1216 : Certifies 1216 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0881.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1217 : Certifies 1217 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0882.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1218 : Certifies 1218 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0883.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1219 : Certifies 1219 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0884.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1220 : Certifies 1220 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0885.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1221 : Certifies 1221 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0886.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1222 : Certifies 1222 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0887.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1223 : Certifies 1223 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0888.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1224 : Certifies 1224 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0889.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1225 : Certifies 1225 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0890.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1226 : Certifies 1226 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0891.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1227 : Certifies 1227 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0892.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1228 : Certifies 1228 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0893.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1229 : Certifies 1229 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0894.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B040 (j : Fin 30) :
    Certifies (1200 + j.val) := by
  fin_cases j
  · exact projection_1200
  · exact projection_1201
  · exact projection_1202
  · exact projection_1203
  · exact projection_1204
  · exact projection_1205
  · exact projection_1206
  · exact projection_1207
  · exact projection_1208
  · exact projection_1209
  · exact projection_1210
  · exact projection_1211
  · exact projection_1212
  · exact projection_1213
  · exact projection_1214
  · exact projection_1215
  · exact projection_1216
  · exact projection_1217
  · exact projection_1218
  · exact projection_1219
  · exact projection_1220
  · exact projection_1221
  · exact projection_1222
  · exact projection_1223
  · exact projection_1224
  · exact projection_1225
  · exact projection_1226
  · exact projection_1227
  · exact projection_1228
  · exact projection_1229

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
