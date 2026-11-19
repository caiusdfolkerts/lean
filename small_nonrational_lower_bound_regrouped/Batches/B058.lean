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
/- Source: ProjectionCertificates/R_one_six_1587.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1587

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 426, 564, 724, 376, 880, 928, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 368, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_426, vertices_564, vertices_724, vertices_376, vertices_880, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_368, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_368) then 19 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_38 197 162 532 548 644 296 560 592 416 672 800 391 331 93 368
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 42 3
cert_row_2 1 3 4 5 7 368
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 42 426 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 3 1 3 5 6 84 724 3
cert_coverFacet 4 376
cert_cover_5 4 1 2 3 4 5 56 376 3
cert_coverFacet 5 880
cert_cover_5 5 1 3 4 5 8 368 880 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1587

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1588.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1588

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 426, 564, 724, 632, 936, 840, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 532, 548, 196, 644, 56, 88, 424, 552, 328, 584, 776, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_426, vertices_564, vertices_724, vertices_632, vertices_936, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_424, vertices_552, vertices_328, vertices_584, vertices_776, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_424), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_424) then 18 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 197 162 532 548 644 552 584 776 560 592 672 391 331 93 424
cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 7 424
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 38 678 3
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 42 426 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 936
cert_cover_5 5 0 2 4 6 8 424 936 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1588

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1589.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1589

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 426, 564, 724, 568, 856, 936, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 162, 386, 52, 84, 532, 548, 196, 644, 56, 88, 536, 424, 552, 328, 776, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_426, vertices_564, vertices_724, vertices_568, vertices_856, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_536, vertices_424, vertices_552, vertices_328, vertices_776, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_162), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_536), (true, vertices_424), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_424) then 18 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 197 162 532 548 644 536 552 776 560 592 672 391 331 93 424
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 2 4 6 7 424
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 42 426 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 936
cert_cover_5 6 1 2 4 6 8 424 936 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1589

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1590.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1590

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 810, 898, 244, 696, 728, 840, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 546, 386, 642, 770, 52, 84, 164, 196, 56, 88, 664, 552, 328, 584, 776, 176, 208, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_810, vertices_898, vertices_244, vertices_696, vertices_728, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_664, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_164), (true, vertices_664), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_176), (true, vertices_208), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_664) then 18 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 197 546 642 770 164 552 584 776 176 208 672 391 331 93 664
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 2 3 6 8 664
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 244
cert_cover_5 3 3 1 3 4 5 52 244 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 728
cert_cover_5 5 1 2 3 5 6 88 728 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1590

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1591.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1591

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 810, 898, 244, 568, 856, 752, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 546, 386, 642, 770, 52, 84, 164, 196, 56, 88, 536, 552, 328, 776, 240, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_810, vertices_898, vertices_244, vertices_568, vertices_856, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_240, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
cert_nodeAtPriority_38 197 546 642 770 164 536 552 776 560 592 672 391 331 93 240
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 8 240 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1591

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1592.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1592

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 554, 906, 244, 568, 856, 752, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 522, 546, 386, 642, 52, 84, 164, 196, 56, 88, 536, 552, 328, 776, 240, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_554, vertices_906, vertices_244, vertices_568, vertices_856, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_522, vertices_546, vertices_386, vertices_642, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_240, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_522), (true, vertices_546), (true, vertices_642), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
cert_nodeAtPriority_38 197 522 546 642 164 536 552 776 560 592 672 391 331 93 240
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 2 6 7 8 906 266 2
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 906
cert_cover_5 2 2 0 2 6 7 266 906 2
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 8 240 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1592

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1593.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1593

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 331, 93, 197, 961, 678, 810, 898, 564, 724, 376, 880, 7, 11, 259, 29, 69, 133, 73, 193, 321, 385, 38, 134, 42, 266, 546, 386, 642, 770, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 368, 560, 592, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_331, vertices_93, vertices_197, vertices_961, vertices_678, vertices_810, vertices_898, vertices_564, vertices_724, vertices_376, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_29, vertices_69, vertices_133, vertices_73, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_368, vertices_560, vertices_592, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_331), (false, vertices_93), (false, vertices_197), (false, vertices_961), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_368) then 19 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_38 197 546 642 770 532 548 644 296 560 592 800 391 331 93 368
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 3 4 5 7 368
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 1 2 3 4 5 56 376 3
cert_coverFacet 6 880
cert_cover_5 6 1 3 4 5 8 368 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1593

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1594.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1594

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 689, 849, 398, 202, 450, 428, 184, 728, 992, 7, 27, 67, 37, 261, 49, 81, 529, 545, 321, 769, 14, 262, 74, 138, 194, 322, 386, 44, 396, 292, 56, 88, 152, 168, 200, 176, 592, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_689, vertices_849, vertices_398, vertices_202, vertices_450, vertices_428, vertices_184, vertices_728, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_292, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_689), (false, vertices_849), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 2 3 5 6 8 728 88 3
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 2 1 4
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 728
cert_cover_5 5 1 2 3 5 6 88 728 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1594

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1595.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1595

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 625, 961, 398, 202, 450, 428, 184, 728, 944, 7, 27, 67, 37, 261, 49, 81, 545, 321, 577, 769, 14, 262, 74, 138, 194, 322, 386, 44, 396, 292, 56, 88, 152, 168, 200, 176, 560, 592, 656, 416, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_625, vertices_961, vertices_398, vertices_202, vertices_450, vertices_428, vertices_184, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_292, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_560, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_625), (false, vertices_961), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_625) then 18 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 2 3 5 6 8 728 88 3
cert_row_4 2 3 4 6 7 8 944 176 3
cert_rows_3
cert_pivot_3 2 1 3
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 728
cert_cover_5 5 1 2 3 5 6 88 728 3
cert_coverFacet 6 944
cert_cover_5 6 2 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1595

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1596.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1596

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 689, 849, 398, 202, 962, 428, 248, 720, 928, 7, 27, 67, 37, 261, 49, 81, 529, 545, 321, 769, 14, 262, 74, 138, 194, 322, 386, 44, 396, 292, 56, 88, 168, 200, 176, 208, 592, 656, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_689, vertices_849, vertices_398, vertices_202, vertices_962, vertices_428, vertices_248, vertices_720, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_292, vertices_56, vertices_88, vertices_168, vertices_200, vertices_176, vertices_208, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_689), (false, vertices_849), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_168), (true, vertices_200), (true, vertices_208), (true, vertices_416), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 248
cert_cover_5 4 2 2 3 4 5 56 248 3
cert_coverFacet 5 720
cert_cover_2 5 5 3 6 8 208 720 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1596

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1597.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1597

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 689, 849, 398, 202, 962, 428, 184, 728, 928, 7, 27, 67, 37, 261, 49, 81, 529, 545, 321, 769, 14, 262, 74, 138, 194, 322, 386, 44, 396, 292, 56, 88, 152, 168, 200, 176, 592, 656, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_689, vertices_849, vertices_398, vertices_202, vertices_962, vertices_428, vertices_184, vertices_728, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_292, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_689), (false, vertices_849), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_416), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 88 728 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1597

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1598.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1598

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 625, 833, 398, 202, 962, 428, 184, 728, 944, 7, 27, 67, 37, 261, 49, 81, 545, 321, 577, 769, 14, 262, 74, 138, 194, 322, 386, 44, 396, 292, 56, 88, 152, 168, 200, 176, 560, 592, 656, 416, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_625, vertices_833, vertices_398, vertices_202, vertices_962, vertices_428, vertices_184, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_292, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_560, vertices_592, vertices_656, vertices_416, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_625), (false, vertices_833), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_656), (true, vertices_416), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_396) then 18 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
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
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 728
cert_cover_5 5 2 2 3 5 6 88 728 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1598

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1599.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1599

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 561, 721, 833, 398, 202, 962, 428, 248, 944, 7, 27, 67, 37, 261, 49, 81, 529, 545, 321, 577, 769, 14, 262, 74, 138, 194, 322, 386, 44, 396, 292, 56, 88, 168, 200, 176, 560, 208, 656, 416, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_561, vertices_721, vertices_833, vertices_398, vertices_202, vertices_962, vertices_428, vertices_248, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_292, vertices_56, vertices_88, vertices_168, vertices_200, vertices_176, vertices_560, vertices_208, vertices_656, vertices_416, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_561), (false, vertices_721), (false, vertices_833), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_396), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_327) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_396) then 16 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 248
cert_cover_5 4 2 2 3 4 5 56 248 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1599

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1600.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1600

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 91, 169, 713, 625, 929, 398, 342, 202, 962, 428, 116, 868, 27, 41, 73, 137, 49, 81, 161, 545, 577, 641, 14, 22, 262, 74, 138, 82, 194, 322, 386, 44, 396, 52, 84, 100, 292, 324, 168, 200, 112, 608, 416, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_169, vertices_713, vertices_625, vertices_929, vertices_398, vertices_342, vertices_202, vertices_962, vertices_428, vertices_116, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_41, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_545, vertices_577, vertices_641, vertices_14, vertices_22, vertices_262, vertices_74, vertices_138, vertices_82, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_84, vertices_100, vertices_292, vertices_324, vertices_168, vertices_200, vertices_112, vertices_608, vertices_416, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_169), (false, vertices_713), (false, vertices_625), (false, vertices_929), (true, vertices_262), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_396), (true, vertices_84), (true, vertices_100), (true, vertices_292), (true, vertices_324), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_713) then 17 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 1 3 5 7 342 22 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 22 342 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 194 962 3
cert_coverFacet 4 428
cert_cover_5 4 0 1 2 4 6 44 428 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1600

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1601.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1601

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 625, 398, 774, 202, 962, 428, 184, 728, 944, 7, 27, 67, 37, 517, 49, 81, 545, 577, 14, 262, 518, 74, 138, 194, 578, 386, 770, 44, 396, 292, 772, 56, 88, 152, 168, 200, 176, 560, 592, 656, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_625, vertices_398, vertices_774, vertices_202, vertices_962, vertices_428, vertices_184, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_262, vertices_518, vertices_74, vertices_138, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_396, vertices_292, vertices_772, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_560, vertices_592, vertices_656, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_625), (true, vertices_262), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_396), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_656), (true, vertices_416), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_583) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_396) then 19 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 428
cert_cover_5 4 0 1 2 4 6 44 428 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 728
cert_cover_5 6 2 2 3 5 6 88 728 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1601

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1602.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1602

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 561, 721, 398, 774, 202, 962, 428, 248, 944, 7, 27, 67, 37, 517, 49, 81, 529, 545, 577, 14, 262, 518, 74, 138, 194, 578, 386, 770, 44, 396, 292, 772, 56, 88, 168, 200, 176, 560, 208, 656, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_561, vertices_721, vertices_398, vertices_774, vertices_202, vertices_962, vertices_428, vertices_248, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_529, vertices_545, vertices_577, vertices_14, vertices_262, vertices_518, vertices_74, vertices_138, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_396, vertices_292, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_176, vertices_560, vertices_208, vertices_656, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_561), (false, vertices_721), (true, vertices_262), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_396), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
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
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 428
cert_cover_5 4 0 1 2 4 6 44 428 3
cert_coverFacet 5 248
cert_cover_5 5 2 2 3 4 5 56 248 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1602

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1603.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1603

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 721, 897, 398, 774, 202, 962, 428, 248, 7, 27, 67, 37, 517, 49, 81, 145, 289, 577, 385, 641, 769, 14, 262, 518, 74, 138, 194, 578, 386, 770, 44, 396, 292, 772, 56, 88, 168, 200, 176, 208, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_721, vertices_897, vertices_398, vertices_774, vertices_202, vertices_962, vertices_428, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_145, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_518, vertices_74, vertices_138, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_396, vertices_292, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_176, vertices_208, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_721), (false, vertices_897), (true, vertices_262), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_396), (true, vertices_168), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_583) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_433) then 17 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_396) then 14 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 428
cert_cover_5 4 0 1 2 4 6 44 428 3
cert_coverFacet 5 248
cert_cover_5 5 2 2 3 4 5 56 248 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1603

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1604.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1604

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 583, 91, 805, 433, 849, 398, 774, 202, 962, 428, 248, 464, 7, 27, 67, 37, 517, 49, 81, 273, 289, 577, 769, 14, 262, 518, 74, 138, 194, 578, 386, 770, 44, 396, 292, 772, 56, 88, 168, 200, 176, 208, 336, 400, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_805, vertices_433, vertices_849, vertices_398, vertices_774, vertices_202, vertices_962, vertices_428, vertices_248, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_517, vertices_49, vertices_81, vertices_273, vertices_289, vertices_577, vertices_769, vertices_14, vertices_262, vertices_518, vertices_74, vertices_138, vertices_194, vertices_578, vertices_386, vertices_770, vertices_44, vertices_396, vertices_292, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_805), (false, vertices_433), (false, vertices_849), (true, vertices_262), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_770), (true, vertices_396), (true, vertices_168), (true, vertices_200), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_433) then 18 else
  if p.val = (false, vertices_849) then 19 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 428
cert_cover_5 4 0 1 2 4 6 44 428 3
cert_coverFacet 5 248
cert_cover_5 5 2 2 3 4 5 56 248 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1604

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1605.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1605

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 91, 707, 613, 369, 398, 902, 202, 812, 312, 472, 992, 7, 27, 67, 515, 37, 517, 49, 81, 97, 577, 14, 390, 518, 74, 138, 194, 642, 44, 268, 548, 772, 56, 88, 280, 296, 200, 392, 304, 336, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_91, vertices_707, vertices_613, vertices_369, vertices_398, vertices_902, vertices_202, vertices_812, vertices_312, vertices_472, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_97, vertices_577, vertices_14, vertices_390, vertices_518, vertices_74, vertices_138, vertices_194, vertices_642, vertices_44, vertices_268, vertices_548, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_200, vertices_392, vertices_304, vertices_336, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_91), (false, vertices_707), (false, vertices_613), (false, vertices_369), (true, vertices_390), (true, vertices_138), (true, vertices_268), (true, vertices_772), (true, vertices_280), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_613) then 12 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_390) then 13 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 8 390 902 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1605

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1606.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1606

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 91, 195, 899, 421, 241, 590, 706, 812, 568, 728, 944, 7, 27, 67, 131, 771, 37, 261, 49, 81, 161, 193, 385, 14, 518, 74, 194, 578, 642, 44, 524, 292, 772, 56, 88, 536, 552, 584, 176, 560, 208, 656, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_91, vertices_195, vertices_899, vertices_421, vertices_241, vertices_590, vertices_706, vertices_812, vertices_568, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_771, vertices_37, vertices_261, vertices_49, vertices_81, vertices_161, vertices_193, vertices_385, vertices_14, vertices_518, vertices_74, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_292, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_176, vertices_560, vertices_208, vertices_656, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_91), (false, vertices_195), (false, vertices_899), (false, vertices_421), (false, vertices_241), (true, vertices_578), (true, vertices_524), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_656), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 10 12 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_421) then 11 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 5 6 8 728 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 728
cert_cover_5 4 2 2 3 5 6 88 728 3
cert_coverFacet 5 944
cert_cover_5 5 3 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1606

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1608.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1608

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 91, 195, 899, 421, 241, 590, 706, 812, 440, 728, 904, 7, 27, 67, 131, 771, 37, 261, 49, 81, 161, 193, 385, 14, 518, 74, 194, 578, 642, 44, 524, 292, 772, 56, 88, 152, 296, 584, 392, 648, 776, 176, 208, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_91, vertices_195, vertices_899, vertices_421, vertices_241, vertices_590, vertices_706, vertices_812, vertices_440, vertices_728, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_771, vertices_37, vertices_261, vertices_49, vertices_81, vertices_161, vertices_193, vertices_385, vertices_14, vertices_518, vertices_74, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_292, vertices_772, vertices_56, vertices_88, vertices_152, vertices_296, vertices_584, vertices_392, vertices_648, vertices_776, vertices_176, vertices_208, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_91), (false, vertices_195), (false, vertices_899), (false, vertices_421), (false, vertices_241), (true, vertices_578), (true, vertices_524), (true, vertices_152), (true, vertices_296), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 10 12 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_421) then 11 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 440
cert_cover_5 3 2 2 3 4 6 56 440 3
cert_coverFacet 4 728
cert_cover_5 4 3 2 3 5 6 88 728 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1608

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1610.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1610

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 421, 241, 270, 326, 842, 300, 964, 824, 728, 944, 7, 27, 67, 37, 133, 49, 81, 161, 193, 14, 70, 262, 74, 266, 322, 44, 268, 292, 196, 324, 388, 56, 88, 536, 296, 584, 776, 176, 816, 208, 656, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_421, vertices_241, vertices_270, vertices_326, vertices_842, vertices_300, vertices_964, vertices_824, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_74, vertices_266, vertices_322, vertices_44, vertices_268, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_296, vertices_584, vertices_776, vertices_176, vertices_816, vertices_208, vertices_656, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_421), (false, vertices_241), (true, vertices_262), (true, vertices_266), (true, vertices_322), (true, vertices_268), (true, vertices_324), (true, vertices_536), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_816), (true, vertices_656), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_816) then 22 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 1 5 6 7 8 964 196 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 964
cert_cover_5 4 2 1 5 6 7 196 964 3
cert_coverFacet 5 824
cert_cover_5 5 0 2 3 4 7 56 824 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coverFacet 7 944
cert_cover_5 7 0 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1610

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1611.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1611

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 421, 689, 721, 270, 326, 842, 300, 964, 632, 936, 7, 27, 67, 37, 133, 49, 81, 657, 161, 193, 14, 70, 262, 74, 266, 322, 44, 268, 292, 196, 324, 388, 56, 88, 296, 552, 584, 776, 560, 592, 416, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_421, vertices_689, vertices_721, vertices_270, vertices_326, vertices_842, vertices_300, vertices_964, vertices_632, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_657, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_74, vertices_266, vertices_322, vertices_44, vertices_268, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_296, vertices_552, vertices_584, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_421), (false, vertices_689), (false, vertices_721), (true, vertices_262), (true, vertices_266), (true, vertices_322), (true, vertices_268), (true, vertices_324), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 262 266 322 268 324 296 552 584 776 832 896 199 91 63 421 689 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_4 1 1 5 6 7 8 964 196 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 964
cert_cover_5 4 1 1 5 6 7 196 964 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 296 936 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1611

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1621.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1621

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 422, 810, 692, 724, 632, 928, 960, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 266, 290, 386, 52, 84, 660, 164, 196, 56, 88, 552, 584, 776, 560, 592, 416, 672, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_422, vertices_810, vertices_692, vertices_724, vertices_632, vertices_928, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_290, vertices_386, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_290), (true, vertices_660), (true, vertices_164), (true, vertices_552), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 18 14 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_841) then 17 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_660) then 19 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 8 632 56 3
cert_row_2 1 1 3 6 8 660
cert_row_4 2 0 1 4 6 7 422 38 3
cert_row_4 3 0 2 4 7 8 810 42 3
cert_rows
cert_pivot_2 5 3 1 0
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 38 422 3
cert_coverFacet 1 810
cert_cover_5 1 3 0 2 4 7 42 810 3
cert_coverFacet 2 692
cert_cover_5 2 1 1 3 4 6 52 692 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 632
cert_cover_5 4 0 2 3 4 5 56 632 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1621

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1622.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1622

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 422, 810, 564, 724, 932, 632, 960, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 266, 290, 386, 52, 84, 532, 420, 548, 196, 644, 56, 88, 552, 584, 776, 560, 592, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_422, vertices_810, vertices_564, vertices_724, vertices_932, vertices_632, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_290, vertices_386, vertices_52, vertices_84, vertices_532, vertices_420, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_560, vertices_592, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_290), (true, vertices_532), (true, vertices_420), (true, vertices_548), (true, vertices_644), (true, vertices_552), (true, vertices_560), (true, vertices_592), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_420) then 17 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 1 4 6 7 420
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 38 422 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 932
cert_cover_5 4 1 1 4 6 8 420 932 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1622

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1623.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1623

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 841, 449, 897, 678, 810, 308, 468, 932, 376, 7, 11, 131, 29, 69, 73, 521, 193, 321, 385, 641, 769, 38, 134, 42, 522, 546, 642, 52, 84, 276, 676, 292, 196, 388, 56, 88, 296, 328, 776, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_841, vertices_449, vertices_897, vertices_678, vertices_810, vertices_308, vertices_468, vertices_932, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_521, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_276, vertices_676, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_841), (false, vertices_449), (false, vertices_897), (true, vertices_546), (true, vertices_276), (true, vertices_676), (true, vertices_292), (true, vertices_388), (true, vertices_296), (true, vertices_304), (true, vertices_336), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_676) then 16 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 1 4 6 8 676
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 308
cert_cover_2 2 3 1 4 7 52 308 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 932
cert_cover_5 4 1 1 4 6 7 676 932 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1623

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1624.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1624

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 841, 449, 897, 678, 810, 436, 468, 376, 928, 7, 11, 131, 29, 69, 73, 521, 193, 321, 385, 641, 769, 38, 134, 42, 522, 546, 642, 52, 84, 404, 164, 196, 56, 88, 296, 328, 776, 304, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_841, vertices_449, vertices_897, vertices_678, vertices_810, vertices_436, vertices_468, vertices_376, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_521, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_404, vertices_164, vertices_196, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_841), (false, vertices_449), (false, vertices_897), (true, vertices_546), (true, vertices_404), (true, vertices_164), (true, vertices_296), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 17 13 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_841) then 16 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_404) then 18 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 7 376 56 3
cert_row_2 1 1 3 6 7 404
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 0 2 4 7 8 810 42 3
cert_rows
cert_pivot_2 5 3 1 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 3 0 2 4 7 42 810 3
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 52 436 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 376
cert_cover_5 4 0 2 3 4 5 56 376 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1624

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1625.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1625

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 523, 899, 93, 841, 449, 678, 554, 244, 824, 472, 944, 7, 11, 131, 515, 29, 69, 73, 521, 193, 321, 385, 769, 38, 134, 42, 522, 546, 642, 52, 84, 164, 196, 56, 88, 280, 552, 328, 776, 176, 816, 208, 400, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_523, vertices_899, vertices_93, vertices_841, vertices_449, vertices_678, vertices_554, vertices_244, vertices_824, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_29, vertices_69, vertices_73, vertices_521, vertices_193, vertices_321, vertices_385, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_88, vertices_280, vertices_552, vertices_328, vertices_776, vertices_176, vertices_816, vertices_208, vertices_400, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_523), (false, vertices_899), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_546), (true, vertices_164), (true, vertices_280), (true, vertices_552), (true, vertices_176), (true, vertices_816), (true, vertices_208), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_841) then 17 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_816) then 19 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 4 7 8 816
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 244
cert_cover_5 2 2 1 3 4 5 52 244 3
cert_coverFacet 3 824
cert_cover_5 3 1 2 3 4 7 56 824 3
cert_coverFacet 4 472
cert_cover_5 4 3 2 3 5 6 88 472 3
cert_coverFacet 5 944
cert_cover_5 5 1 3 4 6 7 176 944 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1625

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1626.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1626

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 523, 899, 93, 841, 449, 678, 554, 436, 468, 376, 936, 7, 11, 131, 515, 29, 69, 73, 521, 193, 321, 385, 769, 38, 134, 42, 522, 546, 642, 52, 84, 404, 164, 196, 56, 88, 296, 552, 328, 776, 304, 336, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_523, vertices_899, vertices_93, vertices_841, vertices_449, vertices_678, vertices_554, vertices_436, vertices_468, vertices_376, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_29, vertices_69, vertices_73, vertices_521, vertices_193, vertices_321, vertices_385, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_404, vertices_164, vertices_196, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_304, vertices_336, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_523), (false, vertices_899), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_546), (true, vertices_404), (true, vertices_164), (true, vertices_296), (true, vertices_552), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 17 13 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_841) then 16 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_404) then 18 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
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
cert_row_2 1 1 3 6 7 404
cert_row_4 2 2 3 4 5 7 376 56 3
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 52 436 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 376
cert_cover_5 4 2 2 3 4 5 56 376 3
cert_coverFacet 5 936
cert_cover_5 5 3 2 4 6 7 296 936 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1626

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1627.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1627

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 421, 689, 721, 142, 458, 812, 396, 568, 856, 992, 7, 27, 67, 37, 133, 49, 81, 657, 161, 193, 14, 134, 74, 138, 194, 44, 140, 268, 292, 388, 56, 88, 536, 552, 328, 392, 776, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_421, vertices_689, vertices_721, vertices_142, vertices_458, vertices_812, vertices_396, vertices_568, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_657, vertices_161, vertices_193, vertices_14, vertices_134, vertices_74, vertices_138, vertices_194, vertices_44, vertices_140, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_392, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_421), (false, vertices_689), (false, vertices_721), (true, vertices_138), (true, vertices_140), (true, vertices_268), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_392), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 138 140 268 536 552 328 392 776 800 448 832 199 91 63 421 689 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 396
cert_cover_2 3 2 1 6 7 140 396 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1627

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1740 : Certifies 1740 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1587.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1741 : Certifies 1741 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1588.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1742 : Certifies 1742 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1589.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1743 : Certifies 1743 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1590.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1744 : Certifies 1744 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1591.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1745 : Certifies 1745 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1592.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1746 : Certifies 1746 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1593.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1747 : Certifies 1747 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1594.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1748 : Certifies 1748 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1595.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1749 : Certifies 1749 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1596.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1750 : Certifies 1750 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1597.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1751 : Certifies 1751 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1598.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1752 : Certifies 1752 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1599.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1753 : Certifies 1753 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1600.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1754 : Certifies 1754 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1601.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1755 : Certifies 1755 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1602.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1756 : Certifies 1756 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1603.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1757 : Certifies 1757 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1604.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1758 : Certifies 1758 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1605.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1759 : Certifies 1759 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1606.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1760 : Certifies 1760 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1608.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1761 : Certifies 1761 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1610.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1762 : Certifies 1762 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1611.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1763 : Certifies 1763 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1621.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1764 : Certifies 1764 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1622.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1765 : Certifies 1765 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1623.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1766 : Certifies 1766 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1624.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1767 : Certifies 1767 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1625.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1768 : Certifies 1768 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1626.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1769 : Certifies 1769 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1627.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B058 (j : Fin 30) :
    Certifies (1740 + j.val) := by
  fin_cases j
  · exact projection_1740
  · exact projection_1741
  · exact projection_1742
  · exact projection_1743
  · exact projection_1744
  · exact projection_1745
  · exact projection_1746
  · exact projection_1747
  · exact projection_1748
  · exact projection_1749
  · exact projection_1750
  · exact projection_1751
  · exact projection_1752
  · exact projection_1753
  · exact projection_1754
  · exact projection_1755
  · exact projection_1756
  · exact projection_1757
  · exact projection_1758
  · exact projection_1759
  · exact projection_1760
  · exact projection_1761
  · exact projection_1762
  · exact projection_1763
  · exact projection_1764
  · exact projection_1765
  · exact projection_1766
  · exact projection_1767
  · exact projection_1768
  · exact projection_1769

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
