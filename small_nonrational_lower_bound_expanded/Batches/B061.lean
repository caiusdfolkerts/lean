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
/- Source: ProjectionCertificates/R_one_six_1688.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1688

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 677, 625, 78, 454, 898, 428, 332, 312, 856, 944, 7, 27, 67, 515, 37, 645, 49, 81, 545, 577, 14, 70, 134, 74, 322, 386, 642, 770, 44, 76, 268, 164, 324, 388, 56, 88, 280, 296, 328, 304, 560, 592, 784, 416, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_677, vertices_625, vertices_78, vertices_454, vertices_898, vertices_428, vertices_332, vertices_312, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_645, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_70, vertices_134, vertices_74, vertices_322, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_268, vertices_164, vertices_324, vertices_388, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_677), (false, vertices_625), (true, vertices_70), (true, vertices_386), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_304), (true, vertices_784), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 1 70 0 386 76 268 324 388 280 296 328 304 784 416 896 647 677 63 91 835 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 44 428 3
cert_coverFacet 4 332
cert_cover_2 4 2 1 5 7 76 332 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 88 856 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1688

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1689.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1689

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 677, 625, 78, 454, 898, 428, 332, 696, 856, 904, 7, 27, 67, 515, 37, 645, 49, 81, 545, 577, 14, 70, 134, 74, 322, 386, 642, 770, 44, 76, 268, 164, 324, 388, 56, 88, 536, 168, 328, 392, 648, 776, 560, 592, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_677, vertices_625, vertices_78, vertices_454, vertices_898, vertices_428, vertices_332, vertices_696, vertices_856, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_645, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_70, vertices_134, vertices_74, vertices_322, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_268, vertices_164, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_168, vertices_328, vertices_392, vertices_648, vertices_776, vertices_560, vertices_592, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_677), (false, vertices_625), (true, vertices_70), (true, vertices_386), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_536), (true, vertices_168), (true, vertices_328), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 1 70 0 386 76 268 324 388 536 168 328 392 648 776 896 647 677 63 91 835 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 44 428 3
cert_coverFacet 4 332
cert_cover_2 4 2 1 5 7 76 332 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1689

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1690.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1690

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 139, 451, 421, 325, 681, 94, 842, 906, 308, 852, 632, 944, 7, 11, 67, 131, 37, 69, 261, 41, 137, 161, 321, 385, 30, 70, 74, 138, 778, 322, 386, 52, 84, 276, 292, 324, 56, 88, 552, 584, 648, 304, 560, 592, 784, 416, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_139, vertices_451, vertices_421, vertices_325, vertices_681, vertices_94, vertices_842, vertices_906, vertices_308, vertices_852, vertices_632, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_37, vertices_69, vertices_261, vertices_41, vertices_137, vertices_161, vertices_321, vertices_385, vertices_30, vertices_70, vertices_74, vertices_138, vertices_778, vertices_322, vertices_386, vertices_52, vertices_84, vertices_276, vertices_292, vertices_324, vertices_56, vertices_88, vertices_552, vertices_584, vertices_648, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_139), (false, vertices_451), (false, vertices_421), (false, vertices_325), (false, vertices_681), (true, vertices_74), (true, vertices_778), (true, vertices_84), (true, vertices_276), (true, vertices_88), (true, vertices_584), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_139) then 1 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_325) then 2 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_778) then 16 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
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
cert_row_4 0 3 4 6 7 8 944 304 2
cert_row_4 1 2 3 4 5 8 632 56 3
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_2 3 0 2 7 8 778
cert_row_2 4 0 1 2 3 30
cert_rows_2
cert_pivot 6 4 5 7 0
cert_heightProof 5
cert_coverFacet 0 94
cert_cover_5 0 4 0 1 2 5 30 94 3
cert_coverFacet 1 842
cert_cover_5 1 3 0 2 5 7 74 842 3
cert_coverFacet 2 906
cert_cover_5 2 3 0 2 6 7 138 906 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 632
cert_cover_5 5 1 2 3 4 5 56 632 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1690

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1691.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1691

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 139, 451, 421, 325, 681, 94, 842, 906, 692, 852, 900, 632, 7, 11, 67, 131, 37, 69, 261, 41, 137, 161, 321, 385, 30, 70, 74, 138, 778, 322, 386, 52, 84, 532, 164, 324, 388, 644, 772, 56, 88, 552, 584, 648, 560, 592, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_139, vertices_451, vertices_421, vertices_325, vertices_681, vertices_94, vertices_842, vertices_906, vertices_692, vertices_852, vertices_900, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_37, vertices_69, vertices_261, vertices_41, vertices_137, vertices_161, vertices_321, vertices_385, vertices_30, vertices_70, vertices_74, vertices_138, vertices_778, vertices_322, vertices_386, vertices_52, vertices_84, vertices_532, vertices_164, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_648, vertices_560, vertices_592, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_139), (false, vertices_451), (false, vertices_421), (false, vertices_325), (false, vertices_681), (true, vertices_74), (true, vertices_778), (true, vertices_84), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_88), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_139) then 1 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_325) then 2 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_778) then 16 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_832) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
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
cert_row_4 0 1 3 4 6 8 692 52 3
cert_row_4 1 2 3 4 5 8 632 56 3
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_2 3 0 2 7 8 778
cert_row_2 4 0 1 2 3 30
cert_rows_2
cert_pivot 6 4 5 7 0
cert_heightProof 5
cert_coverFacet 0 94
cert_cover_5 0 4 0 1 2 5 30 94 3
cert_coverFacet 1 842
cert_cover_5 1 3 0 2 5 7 74 842 3
cert_coverFacet 2 906
cert_cover_5 2 3 0 2 6 7 138 906 3
cert_coverFacet 3 692
cert_cover_5 3 0 1 3 4 6 52 692 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 632
cert_cover_5 6 1 2 3 4 5 56 632 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1691

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1692.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1692

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 91, 229, 433, 721, 782, 454, 586, 962, 428, 824, 600, 912, 7, 27, 67, 37, 69, 49, 81, 145, 161, 193, 14, 70, 262, 74, 522, 450, 578, 770, 44, 268, 164, 196, 388, 56, 88, 536, 296, 584, 776, 304, 592, 400, 656, 784, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_91, vertices_229, vertices_433, vertices_721, vertices_782, vertices_454, vertices_586, vertices_962, vertices_428, vertices_824, vertices_600, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_69, vertices_49, vertices_81, vertices_145, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_74, vertices_522, vertices_450, vertices_578, vertices_770, vertices_44, vertices_268, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_296, vertices_584, vertices_776, vertices_304, vertices_592, vertices_400, vertices_656, vertices_784, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_91), (false, vertices_229), (false, vertices_433), (false, vertices_721), (true, vertices_262), (true, vertices_522), (true, vertices_450), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_536), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_450) then 15 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 7 450
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 8 450 962 3
cert_coverFacet 4 428
cert_cover_5 4 2 1 2 4 6 44 428 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1692

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1693.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1693

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 91, 229, 561, 721, 929, 782, 454, 586, 962, 428, 824, 600, 7, 27, 67, 37, 69, 49, 81, 529, 161, 545, 193, 641, 14, 70, 262, 74, 522, 450, 578, 770, 44, 268, 164, 196, 388, 56, 88, 536, 296, 584, 776, 560, 592, 416, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_91, vertices_229, vertices_561, vertices_721, vertices_929, vertices_782, vertices_454, vertices_586, vertices_962, vertices_428, vertices_824, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_69, vertices_49, vertices_81, vertices_529, vertices_161, vertices_545, vertices_193, vertices_641, vertices_14, vertices_70, vertices_262, vertices_74, vertices_522, vertices_450, vertices_578, vertices_770, vertices_44, vertices_268, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_296, vertices_584, vertices_776, vertices_560, vertices_592, vertices_416, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_91), (false, vertices_229), (false, vertices_561), (false, vertices_721), (false, vertices_929), (true, vertices_262), (true, vertices_522), (true, vertices_450), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_536), (true, vertices_296), (true, vertices_584), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_450) then 14 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_450), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 7 450
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 8 450 962 3
cert_coverFacet 4 428
cert_cover_5 4 2 1 2 4 6 44 428 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1693

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1694.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1694

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 91, 229, 689, 465, 526, 454, 902, 842, 684, 824, 344, 912, 7, 27, 67, 37, 69, 49, 81, 145, 161, 193, 14, 70, 390, 518, 74, 522, 322, 770, 44, 524, 164, 196, 644, 56, 88, 280, 552, 328, 776, 560, 336, 400, 656, 784, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_91, vertices_229, vertices_689, vertices_465, vertices_526, vertices_454, vertices_902, vertices_842, vertices_684, vertices_824, vertices_344, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_69, vertices_49, vertices_81, vertices_145, vertices_161, vertices_193, vertices_14, vertices_70, vertices_390, vertices_518, vertices_74, vertices_522, vertices_322, vertices_770, vertices_44, vertices_524, vertices_164, vertices_196, vertices_644, vertices_56, vertices_88, vertices_280, vertices_552, vertices_328, vertices_776, vertices_560, vertices_336, vertices_400, vertices_656, vertices_784, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_91), (false, vertices_229), (false, vertices_689), (false, vertices_465), (true, vertices_390), (true, vertices_518), (true, vertices_522), (true, vertices_322), (true, vertices_770), (true, vertices_524), (true, vertices_644), (true, vertices_280), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_390) then 15 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_2 1 0 1 6 7 390
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 902
cert_cover_5 2 1 0 1 6 8 390 902 3
cert_coverFacet 3 842
cert_cover_5 3 0 0 2 5 7 74 842 3
cert_coverFacet 4 684
cert_cover_5 4 2 1 2 4 6 44 684 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1694

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1695.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1695

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 91, 229, 305, 465, 929, 526, 454, 902, 842, 684, 824, 344, 7, 27, 67, 37, 69, 49, 81, 273, 161, 289, 193, 385, 14, 70, 390, 518, 74, 522, 322, 770, 44, 524, 164, 196, 644, 56, 88, 280, 552, 328, 776, 304, 336, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_91, vertices_229, vertices_305, vertices_465, vertices_929, vertices_526, vertices_454, vertices_902, vertices_842, vertices_684, vertices_824, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_69, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_385, vertices_14, vertices_70, vertices_390, vertices_518, vertices_74, vertices_522, vertices_322, vertices_770, vertices_44, vertices_524, vertices_164, vertices_196, vertices_644, vertices_56, vertices_88, vertices_280, vertices_552, vertices_328, vertices_776, vertices_304, vertices_336, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_91), (false, vertices_229), (false, vertices_305), (false, vertices_465), (false, vertices_929), (true, vertices_390), (true, vertices_518), (true, vertices_522), (true, vertices_322), (true, vertices_770), (true, vertices_524), (true, vertices_644), (true, vertices_280), (true, vertices_552), (true, vertices_328), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_390) then 14 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 74 3
cert_row_2 1 0 1 6 7 390
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 902
cert_cover_5 2 1 0 1 6 8 390 902 3
cert_coverFacet 3 842
cert_cover_5 3 0 0 2 5 7 74 842 3
cert_coverFacet 4 684
cert_cover_5 4 2 1 2 4 6 44 684 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1695

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1696.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1696

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 91, 195, 805, 709, 625, 270, 902, 458, 300, 440, 728, 944, 7, 27, 67, 131, 37, 133, 517, 49, 81, 545, 193, 577, 14, 134, 262, 74, 266, 194, 386, 44, 268, 292, 644, 772, 56, 88, 152, 296, 200, 392, 432, 560, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_91, vertices_195, vertices_805, vertices_709, vertices_625, vertices_270, vertices_902, vertices_458, vertices_300, vertices_440, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_517, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_14, vertices_134, vertices_262, vertices_74, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_292, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_296, vertices_200, vertices_392, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_709), (false, vertices_625), (true, vertices_262), (true, vertices_266), (true, vertices_386), (true, vertices_268), (true, vertices_152), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_432), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 18 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_432) then 21 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 134 902 3
cert_coverFacet 2 458
cert_cover_5 2 2 0 2 5 6 74 458 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 728
cert_cover_5 5 3 2 3 5 6 88 728 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1696

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1697.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1697

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 899, 805, 681, 94, 198, 390, 372, 452, 824, 728, 976, 7, 11, 131, 259, 37, 261, 41, 137, 545, 641, 769, 30, 70, 134, 262, 74, 194, 386, 52, 84, 292, 196, 324, 388, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_899, vertices_805, vertices_681, vertices_94, vertices_198, vertices_390, vertices_372, vertices_452, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_37, vertices_261, vertices_41, vertices_137, vertices_545, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_262, vertices_74, vertices_194, vertices_386, vertices_52, vertices_84, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_899), (false, vertices_805), (false, vertices_681), (true, vertices_70), (true, vertices_134), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_88), (true, vertices_536), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_720) then 22 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 372
cert_cover_5 3 2 1 3 4 5 52 372 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 728
cert_cover_5 6 0 2 3 5 6 88 728 3
cert_coverFacet 7 976
cert_cover_5 7 0 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1697

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1698.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1698

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 899, 805, 681, 94, 198, 390, 308, 468, 632, 968, 880, 7, 11, 131, 259, 37, 261, 41, 137, 545, 641, 769, 30, 70, 134, 262, 74, 194, 386, 52, 84, 276, 292, 196, 388, 56, 88, 552, 200, 584, 648, 624, 304, 336, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_899, vertices_805, vertices_681, vertices_94, vertices_198, vertices_390, vertices_308, vertices_468, vertices_632, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_37, vertices_261, vertices_41, vertices_137, vertices_545, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_262, vertices_74, vertices_194, vertices_386, vertices_52, vertices_84, vertices_276, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_200, vertices_584, vertices_648, vertices_624, vertices_304, vertices_336, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_899), (false, vertices_805), (false, vertices_681), (true, vertices_70), (true, vertices_134), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_88), (true, vertices_584), (true, vertices_624), (true, vertices_304), (true, vertices_336), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_624) then 22 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 8 624
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 84 468 3
cert_coverFacet 5 632
cert_cover_5 5 0 2 3 4 5 56 632 3
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 200 968 3
cert_coverFacet 7 880
cert_cover_5 7 0 3 4 5 7 624 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1698

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1699.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1699

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 625, 961, 270, 902, 202, 394, 812, 824, 472, 848, 7, 27, 67, 37, 133, 49, 81, 545, 193, 577, 641, 14, 134, 262, 74, 138, 266, 194, 386, 44, 268, 548, 644, 772, 56, 88, 280, 808, 200, 392, 560, 336, 592, 784, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_625, vertices_961, vertices_270, vertices_902, vertices_202, vertices_394, vertices_812, vertices_824, vertices_472, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_134, vertices_262, vertices_74, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_808, vertices_200, vertices_392, vertices_560, vertices_336, vertices_592, vertices_784, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_625), (false, vertices_961), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_268), (true, vertices_772), (true, vertices_280), (true, vertices_808), (true, vertices_200), (true, vertices_392), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_808) then 18 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 7 8 808
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_rows_3
cert_pivot_3 0 4 2
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 902
cert_cover_5 1 1 0 1 6 7 134 902 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 44 812 3
cert_coverFacet 5 824
cert_cover_5 5 0 2 3 4 7 56 824 3
cert_coverFacet 6 472
cert_cover_5 6 2 2 3 5 6 88 472 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1699

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1700.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1700

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 707, 677, 625, 270, 202, 394, 812, 964, 824, 472, 848, 7, 27, 67, 131, 37, 133, 49, 81, 545, 577, 641, 14, 262, 74, 138, 266, 194, 386, 44, 268, 548, 388, 644, 772, 56, 88, 280, 808, 200, 392, 560, 336, 592, 784, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_707, vertices_677, vertices_625, vertices_270, vertices_202, vertices_394, vertices_812, vertices_964, vertices_824, vertices_472, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_577, vertices_641, vertices_14, vertices_262, vertices_74, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_808, vertices_200, vertices_392, vertices_560, vertices_336, vertices_592, vertices_784, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_707), (false, vertices_677), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_268), (true, vertices_772), (true, vertices_280), (true, vertices_808), (true, vertices_200), (true, vertices_392), (true, vertices_336), (true, vertices_784), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_677) then 13 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_808) then 19 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
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
cert_row_2 0 2 4 7 8 808
cert_row_4 1 1 5 6 7 8 964 388 1
cert_row_4 2 2 3 5 6 7 472 88 3
cert_rows_3
cert_pivot_3 1 4 2
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 812
cert_cover_5 3 0 1 2 4 7 44 812 3
cert_coverFacet 4 964
cert_cover_5 4 1 1 5 6 7 388 964 1
cert_coverFacet 5 824
cert_cover_5 5 0 2 3 4 7 56 824 3
cert_coverFacet 6 472
cert_cover_5 6 2 2 3 5 6 88 472 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1700

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1701.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1701

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 395, 805, 681, 961, 94, 198, 390, 714, 308, 468, 632, 880, 7, 11, 259, 37, 261, 41, 137, 545, 385, 641, 769, 30, 70, 134, 262, 74, 138, 194, 386, 52, 84, 276, 292, 196, 388, 56, 88, 552, 584, 648, 624, 304, 336, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_395, vertices_805, vertices_681, vertices_961, vertices_94, vertices_198, vertices_390, vertices_714, vertices_308, vertices_468, vertices_632, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_37, vertices_261, vertices_41, vertices_137, vertices_545, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_134, vertices_262, vertices_74, vertices_138, vertices_194, vertices_386, vertices_52, vertices_84, vertices_276, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_648, vertices_624, vertices_304, vertices_336, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_395), (false, vertices_805), (false, vertices_681), (false, vertices_961), (true, vertices_70), (true, vertices_134), (true, vertices_74), (true, vertices_194), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_88), (true, vertices_584), (true, vertices_624), (true, vertices_304), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_624) then 21 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 8 624
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_2 2 0 1 2 3 30
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 2 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 714
cert_cover_5 3 1 0 2 5 6 74 714 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 84 468 3
cert_coverFacet 6 632
cert_cover_5 6 0 2 3 4 5 56 632 3
cert_coverFacet 7 880
cert_cover_5 7 0 3 4 5 7 624 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1701

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1702.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1702

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 805, 689, 849, 270, 202, 394, 962, 684, 908, 248, 720, 7, 27, 67, 37, 261, 49, 81, 529, 545, 321, 769, 14, 262, 74, 138, 266, 194, 322, 386, 44, 652, 268, 548, 772, 56, 88, 168, 200, 392, 176, 208, 592, 656, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_805, vertices_689, vertices_849, vertices_270, vertices_202, vertices_394, vertices_962, vertices_684, vertices_908, vertices_248, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_261, vertices_49, vertices_81, vertices_529, vertices_545, vertices_321, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_652, vertices_268, vertices_548, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_392, vertices_176, vertices_208, vertices_592, vertices_656, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_805), (false, vertices_689), (false, vertices_849), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_652), (true, vertices_268), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_208), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_327) then 12 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_652) then 17 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 684
cert_cover_5 4 0 1 2 4 6 44 684 3
cert_coverFacet 5 908
cert_cover_5 5 0 1 2 6 7 652 908 3
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 56 248 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1702

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1703.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1703

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 91, 165, 901, 689, 849, 270, 202, 394, 962, 428, 632, 744, 7, 27, 67, 37, 133, 261, 49, 81, 529, 161, 321, 641, 769, 14, 262, 74, 138, 266, 194, 322, 386, 44, 268, 164, 388, 56, 88, 616, 168, 200, 392, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_165, vertices_901, vertices_689, vertices_849, vertices_270, vertices_202, vertices_394, vertices_962, vertices_428, vertices_632, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_261, vertices_49, vertices_81, vertices_529, vertices_161, vertices_321, vertices_641, vertices_769, vertices_14, vertices_262, vertices_74, vertices_138, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_164, vertices_388, vertices_56, vertices_88, vertices_616, vertices_168, vertices_200, vertices_392, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_165), (false, vertices_901), (false, vertices_689), (false, vertices_849), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_268), (true, vertices_616), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_327) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_901) then 15 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_616) then 17 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_616), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
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
cert_row_2 1 2 4 5 8 616
cert_row_4 2 1 2 4 6 7 428 44 3
cert_rows_3
cert_pivot_3 5 0 1
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 202
cert_cover_2 1 2 0 5 6 74 202 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 7 194 962 3
cert_coverFacet 4 428
cert_cover_5 4 2 1 2 4 6 44 428 3
cert_coverFacet 5 632
cert_cover_5 5 1 2 3 4 5 56 632 3
cert_coverFacet 6 744
cert_cover_5 6 1 2 4 5 6 616 744 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1703

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1704.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1704

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 677, 809, 94, 198, 390, 450, 244, 900, 696, 856, 976, 7, 11, 259, 37, 517, 41, 265, 545, 769, 30, 70, 134, 262, 74, 194, 322, 386, 52, 84, 164, 196, 388, 644, 772, 56, 88, 536, 552, 328, 776, 176, 208, 848, 656, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_677, vertices_809, vertices_94, vertices_198, vertices_390, vertices_450, vertices_244, vertices_900, vertices_696, vertices_856, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_37, vertices_517, vertices_41, vertices_265, vertices_545, vertices_769, vertices_30, vertices_70, vertices_134, vertices_262, vertices_74, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_208, vertices_848, vertices_656, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_677), (false, vertices_809), (true, vertices_70), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_84), (true, vertices_196), (true, vertices_388), (true, vertices_88), (true, vertices_536), (true, vertices_176), (true, vertices_208), (true, vertices_848), (true, vertices_656), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_848) then 23 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_848), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 3 5 7 8 848
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 856
cert_cover_5 7 1 2 3 5 7 88 856 3
cert_coverFacet 8 976
cert_cover_5 8 1 3 5 6 7 208 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1704

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1706.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1706

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 421, 809, 94, 198, 390, 706, 898, 244, 440, 856, 976, 7, 11, 515, 37, 261, 41, 521, 289, 769, 30, 70, 134, 262, 74, 194, 578, 386, 642, 770, 52, 84, 164, 196, 388, 56, 88, 280, 296, 584, 776, 176, 208, 848, 400, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_421, vertices_809, vertices_94, vertices_198, vertices_390, vertices_706, vertices_898, vertices_244, vertices_440, vertices_856, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_37, vertices_261, vertices_41, vertices_521, vertices_289, vertices_769, vertices_30, vertices_70, vertices_134, vertices_262, vertices_74, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_208, vertices_848, vertices_400, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_421), (false, vertices_809), (true, vertices_70), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_280), (true, vertices_176), (true, vertices_208), (true, vertices_848), (true, vertices_400), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_848) then 23 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_848), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
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
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 706
cert_cover_2 3 5 0 6 8 194 706 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 52 244 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 56 440 3
cert_coverFacet 7 856
cert_cover_5 7 1 2 3 5 7 88 856 3
cert_coverFacet 8 976
cert_cover_5 8 1 3 5 6 7 208 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1706

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1707.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1707

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 93, 197, 389, 961, 422, 810, 244, 440, 600, 920, 720, 7, 11, 515, 29, 69, 133, 261, 73, 193, 577, 385, 769, 38, 262, 42, 522, 290, 770, 52, 84, 164, 196, 388, 56, 88, 408, 536, 296, 584, 776, 176, 208, 592, 656, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_93, vertices_197, vertices_389, vertices_961, vertices_422, vertices_810, vertices_244, vertices_440, vertices_600, vertices_920, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_29, vertices_69, vertices_133, vertices_261, vertices_73, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_42, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_408, vertices_536, vertices_296, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_93), (false, vertices_197), (false, vertices_389), (false, vertices_961), (true, vertices_290), (true, vertices_164), (true, vertices_408), (true, vertices_536), (true, vertices_296), (true, vertices_776), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_408) then 19 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 2 3 6 7 408
cert_row_4 2 0 1 4 6 7 422 38 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 38 422 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 3 1 3 4 5 52 244 3
cert_coverFacet 3 440
cert_cover_5 3 1 2 3 4 6 56 440 3
cert_coverFacet 4 600
cert_cover_2 4 3 2 5 8 88 600 3
cert_coverFacet 5 920
cert_cover_5 5 1 2 3 6 8 408 920 3
cert_coverFacet 6 720
cert_cover_2 6 5 3 6 8 208 720 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1707

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1708.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1708

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 93, 197, 389, 961, 422, 810, 244, 824, 728, 432, 912, 7, 11, 515, 29, 69, 133, 261, 73, 193, 577, 385, 769, 38, 262, 42, 522, 290, 770, 52, 84, 164, 196, 388, 56, 88, 536, 808, 584, 176, 304, 208, 400, 656, 784, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_93, vertices_197, vertices_389, vertices_961, vertices_422, vertices_810, vertices_244, vertices_824, vertices_728, vertices_432, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_29, vertices_69, vertices_133, vertices_261, vertices_73, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_42, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_808, vertices_584, vertices_176, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_93), (false, vertices_197), (false, vertices_389), (false, vertices_961), (true, vertices_290), (true, vertices_164), (true, vertices_536), (true, vertices_808), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_808) then 19 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 38 3
cert_row_2 1 2 4 7 8 808
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 38 422 3
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 2 1 3 4 5 52 244 3
cert_coverFacet 3 824
cert_cover_5 3 1 2 3 4 7 56 824 3
cert_coverFacet 4 728
cert_cover_5 4 3 2 3 5 6 88 728 3
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1708

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1709.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1709

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 93, 197, 389, 961, 422, 298, 778, 244, 824, 728, 944, 7, 11, 515, 29, 69, 133, 261, 73, 193, 577, 385, 769, 38, 262, 42, 266, 522, 290, 770, 52, 84, 164, 196, 388, 56, 88, 536, 296, 584, 776, 176, 816, 208, 656, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_93, vertices_197, vertices_389, vertices_961, vertices_422, vertices_298, vertices_778, vertices_244, vertices_824, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_29, vertices_69, vertices_133, vertices_261, vertices_73, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_42, vertices_266, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_296, vertices_584, vertices_776, vertices_176, vertices_816, vertices_208, vertices_656, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_93), (false, vertices_197), (false, vertices_389), (false, vertices_961), (true, vertices_266), (true, vertices_290), (true, vertices_164), (true, vertices_536), (true, vertices_296), (true, vertices_776), (true, vertices_176), (true, vertices_816), (true, vertices_208), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_816) then 20 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 38 3
cert_row_2 1 3 4 7 8 816
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 38 422 3
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 52 244 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 728
cert_cover_5 5 3 2 3 5 6 88 728 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1709

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1710.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1710

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 93, 197, 389, 961, 422, 810, 244, 312, 728, 920, 432, 7, 11, 515, 29, 69, 133, 261, 73, 193, 577, 385, 769, 38, 262, 42, 522, 290, 770, 52, 84, 164, 196, 388, 56, 88, 664, 280, 296, 584, 776, 176, 304, 208, 400, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_93, vertices_197, vertices_389, vertices_961, vertices_422, vertices_810, vertices_244, vertices_312, vertices_728, vertices_920, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_29, vertices_69, vertices_133, vertices_261, vertices_73, vertices_193, vertices_577, vertices_385, vertices_769, vertices_38, vertices_262, vertices_42, vertices_522, vertices_290, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_664, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_93), (false, vertices_197), (false, vertices_389), (false, vertices_961), (true, vertices_290), (true, vertices_164), (true, vertices_664), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_664) then 19 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 6 244 52 3
cert_row_2 1 2 3 6 8 664
cert_row_4 2 0 1 4 6 7 422 38 3
cert_row_4 3 0 2 4 7 8 810 42 3
cert_rows
cert_pivot_2 5 3 1 0
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 38 422 3
cert_coverFacet 1 810
cert_cover_5 1 3 0 2 4 7 42 810 3
cert_coverFacet 2 244
cert_cover_5 2 0 1 3 4 5 52 244 3
cert_coverFacet 3 312
cert_cover_2 3 3 2 4 7 56 312 3
cert_coverFacet 4 728
cert_cover_5 4 1 2 3 5 6 88 728 3
cert_coverFacet 5 920
cert_cover_5 5 1 2 3 6 7 664 920 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1710

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1711.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1711

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 587, 421, 809, 94, 198, 390, 962, 244, 440, 600, 792, 976, 7, 11, 515, 37, 261, 41, 521, 289, 769, 30, 70, 134, 262, 74, 194, 578, 386, 770, 52, 84, 164, 196, 388, 56, 88, 280, 536, 296, 584, 776, 176, 208, 592, 400, 784, 416, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_587, vertices_421, vertices_809, vertices_94, vertices_198, vertices_390, vertices_962, vertices_244, vertices_440, vertices_600, vertices_792, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_37, vertices_261, vertices_41, vertices_521, vertices_289, vertices_769, vertices_30, vertices_70, vertices_134, vertices_262, vertices_74, vertices_194, vertices_578, vertices_386, vertices_770, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_400, vertices_784, vertices_416, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_587), (false, vertices_421), (false, vertices_809), (true, vertices_70), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_176), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_784), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_960) then 25 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 5 6 7 8 960
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 56 440 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 976
cert_cover_5 8 1 3 5 6 7 208 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1711

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1712.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1712

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 525, 661, 809, 369, 209, 961, 782, 214, 902, 122, 202, 394, 488, 13, 21, 517, 41, 521, 49, 81, 145, 289, 193, 321, 641, 769, 14, 22, 134, 774, 58, 74, 138, 266, 82, 194, 386, 524, 148, 644, 104, 296, 200, 392, 776, 112, 208, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_525, vertices_661, vertices_809, vertices_369, vertices_209, vertices_961, vertices_782, vertices_214, vertices_902, vertices_122, vertices_202, vertices_394, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_41, vertices_521, vertices_49, vertices_81, vertices_145, vertices_289, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_134, vertices_774, vertices_58, vertices_74, vertices_138, vertices_266, vertices_82, vertices_194, vertices_386, vertices_524, vertices_148, vertices_644, vertices_104, vertices_296, vertices_200, vertices_392, vertices_776, vertices_112, vertices_208, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_525), (false, vertices_661), (false, vertices_809), (false, vertices_369), (false, vertices_209), (false, vertices_961), (true, vertices_134), (true, vertices_774), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_194), (true, vertices_386), (true, vertices_104), (true, vertices_200), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_774) then 13 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_82) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 1 3 5 6 214 22 3
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 5 22 214 3
cert_coverFacet 2 902
cert_cover_5 2 0 0 1 6 7 134 902 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 5 58 122 3
cert_coverFacet 4 202
cert_cover_2 4 2 0 5 6 74 202 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1712

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1713.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1713

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 625, 961, 782, 902, 202, 394, 556, 824, 472, 848, 7, 27, 67, 37, 133, 49, 81, 545, 193, 577, 641, 14, 134, 774, 74, 138, 266, 194, 386, 44, 524, 548, 644, 56, 88, 280, 552, 200, 392, 776, 560, 336, 592, 784, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_625, vertices_961, vertices_782, vertices_902, vertices_202, vertices_394, vertices_556, vertices_824, vertices_472, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_134, vertices_774, vertices_74, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_280, vertices_552, vertices_200, vertices_392, vertices_776, vertices_560, vertices_336, vertices_592, vertices_784, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_625), (false, vertices_961), (true, vertices_774), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_524), (true, vertices_280), (true, vertices_552), (true, vertices_200), (true, vertices_392), (true, vertices_776), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 11 13 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 17 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_625) then 15 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_774) then 18 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_rows_3
cert_pivot_3 4 0 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 472
cert_cover_5 6 2 2 3 5 6 88 472 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1713

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1714.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1714

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 369, 801, 961, 782, 902, 202, 394, 556, 824, 472, 7, 27, 67, 37, 133, 49, 81, 289, 545, 193, 321, 641, 769, 14, 134, 774, 74, 138, 266, 194, 386, 44, 524, 548, 644, 56, 88, 280, 552, 200, 392, 776, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_369, vertices_801, vertices_961, vertices_782, vertices_902, vertices_202, vertices_394, vertices_556, vertices_824, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_134, vertices_774, vertices_74, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_280, vertices_552, vertices_200, vertices_392, vertices_776, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_369), (false, vertices_801), (false, vertices_961), (true, vertices_774), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_524), (true, vertices_280), (true, vertices_552), (true, vertices_200), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 10 12 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_91) then 11 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_369) then 14 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_776) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_rows_3
cert_pivot_3 4 0 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 472
cert_cover_5 6 2 2 3 5 6 88 472 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1714

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1715.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1715

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 525, 597, 809, 369, 961, 782, 214, 902, 122, 202, 394, 708, 488, 13, 21, 517, 41, 521, 49, 81, 289, 321, 577, 769, 14, 22, 134, 774, 58, 74, 138, 266, 82, 194, 386, 524, 84, 196, 580, 644, 104, 296, 200, 392, 776, 112, 352, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_525, vertices_597, vertices_809, vertices_369, vertices_961, vertices_782, vertices_214, vertices_902, vertices_122, vertices_202, vertices_394, vertices_708, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_41, vertices_521, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_14, vertices_22, vertices_134, vertices_774, vertices_58, vertices_74, vertices_138, vertices_266, vertices_82, vertices_194, vertices_386, vertices_524, vertices_84, vertices_196, vertices_580, vertices_644, vertices_104, vertices_296, vertices_200, vertices_392, vertices_776, vertices_112, vertices_352, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_525), (false, vertices_597), (false, vertices_809), (false, vertices_369), (false, vertices_961), (true, vertices_134), (true, vertices_774), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_194), (true, vertices_386), (true, vertices_196), (true, vertices_644), (true, vertices_104), (true, vertices_200), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_774) then 14 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 1 3 5 6 214 22 3
cert_row_2 2 0 2 3 4 58
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 1 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 214
cert_cover_5 1 1 0 1 3 5 22 214 3
cert_coverFacet 2 902
cert_cover_5 2 0 0 1 6 7 134 902 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 5 58 122 3
cert_coverFacet 4 202
cert_cover_2 4 2 0 5 6 74 202 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1715

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1716.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1716

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 293, 369, 961, 590, 710, 684, 420, 568, 856, 944, 7, 27, 67, 131, 37, 261, 49, 81, 289, 193, 321, 385, 14, 582, 134, 74, 194, 44, 524, 164, 292, 388, 644, 56, 88, 536, 552, 584, 304, 560, 336, 784, 416, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_293, vertices_369, vertices_961, vertices_590, vertices_710, vertices_684, vertices_420, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_289, vertices_193, vertices_321, vertices_385, vertices_14, vertices_582, vertices_134, vertices_74, vertices_194, vertices_44, vertices_524, vertices_164, vertices_292, vertices_388, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_293), (false, vertices_369), (false, vertices_961), (true, vertices_582), (true, vertices_524), (true, vertices_164), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_784), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 12 14 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_369) then 16 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_582) then 19 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 582 710 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 420
cert_cover_2 3 4 1 6 7 164 420 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1716

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1717.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1717

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 293, 817, 465, 590, 710, 684, 420, 568, 856, 992, 7, 27, 67, 131, 37, 261, 49, 81, 273, 289, 193, 385, 14, 582, 134, 74, 194, 44, 524, 164, 292, 388, 644, 56, 88, 536, 552, 584, 560, 336, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_293, vertices_817, vertices_465, vertices_590, vertices_710, vertices_684, vertices_420, vertices_568, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_385, vertices_14, vertices_582, vertices_134, vertices_74, vertices_194, vertices_44, vertices_524, vertices_164, vertices_292, vertices_388, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_584, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_293), (false, vertices_817), (false, vertices_465), (true, vertices_582), (true, vertices_524), (true, vertices_164), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_416), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 12 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 19 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_582) then 20 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
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
cert_coverFacet 3 420
cert_cover_2 3 4 1 6 7 164 420 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1717

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1718.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1718

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 91, 195, 293, 369, 961, 590, 710, 684, 420, 440, 856, 904, 7, 27, 67, 131, 37, 261, 49, 81, 289, 193, 321, 385, 14, 582, 134, 74, 194, 44, 524, 164, 292, 388, 644, 56, 88, 280, 168, 584, 392, 648, 776, 304, 336, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_195, vertices_293, vertices_369, vertices_961, vertices_590, vertices_710, vertices_684, vertices_420, vertices_440, vertices_856, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_289, vertices_193, vertices_321, vertices_385, vertices_14, vertices_582, vertices_134, vertices_74, vertices_194, vertices_44, vertices_524, vertices_164, vertices_292, vertices_388, vertices_644, vertices_56, vertices_88, vertices_280, vertices_168, vertices_584, vertices_392, vertices_648, vertices_776, vertices_304, vertices_336, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_195), (false, vertices_293), (false, vertices_369), (false, vertices_961), (true, vertices_582), (true, vertices_524), (true, vertices_164), (true, vertices_644), (true, vertices_280), (true, vertices_168), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 12 14 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_369) then 16 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_582) then 19 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_582), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 582 710 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 420
cert_cover_2 3 4 1 6 7 164 420 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1718

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1830 : Certifies 1830 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1688.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1831 : Certifies 1831 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1689.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1832 : Certifies 1832 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1690.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1833 : Certifies 1833 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1691.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1834 : Certifies 1834 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1692.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1835 : Certifies 1835 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1693.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1836 : Certifies 1836 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1694.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1837 : Certifies 1837 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1695.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1838 : Certifies 1838 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1696.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1839 : Certifies 1839 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1697.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1840 : Certifies 1840 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1698.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1841 : Certifies 1841 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1699.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1842 : Certifies 1842 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1700.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1843 : Certifies 1843 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1701.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1844 : Certifies 1844 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1702.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1845 : Certifies 1845 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1703.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1846 : Certifies 1846 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1704.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1847 : Certifies 1847 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1706.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1848 : Certifies 1848 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1707.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1849 : Certifies 1849 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1708.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1850 : Certifies 1850 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1709.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1851 : Certifies 1851 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1710.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1852 : Certifies 1852 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1711.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1853 : Certifies 1853 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1712.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1854 : Certifies 1854 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1713.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1855 : Certifies 1855 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1714.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1856 : Certifies 1856 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1715.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1857 : Certifies 1857 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1716.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1858 : Certifies 1858 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1717.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1859 : Certifies 1859 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1718.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B061 (j : Fin 30) :
    Certifies (1830 + j.val) := by
  fin_cases j
  · exact projection_1830
  · exact projection_1831
  · exact projection_1832
  · exact projection_1833
  · exact projection_1834
  · exact projection_1835
  · exact projection_1836
  · exact projection_1837
  · exact projection_1838
  · exact projection_1839
  · exact projection_1840
  · exact projection_1841
  · exact projection_1842
  · exact projection_1843
  · exact projection_1844
  · exact projection_1845
  · exact projection_1846
  · exact projection_1847
  · exact projection_1848
  · exact projection_1849
  · exact projection_1850
  · exact projection_1851
  · exact projection_1852
  · exact projection_1853
  · exact projection_1854
  · exact projection_1855
  · exact projection_1856
  · exact projection_1857
  · exact projection_1858
  · exact projection_1859

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
