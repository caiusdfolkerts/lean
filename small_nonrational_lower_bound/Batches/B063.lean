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
/- Source: ProjectionCertificates/R_one_six_1750.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1750

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 166, 682, 436, 852, 452, 632, 904, 944, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 138, 162, 52, 84, 276, 164, 196, 324, 388, 56, 88, 552, 584, 392, 648, 776, 432, 560, 592, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_166, vertices_682, vertices_436, vertices_852, vertices_452, vertices_632, vertices_904, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_138, vertices_162, vertices_52, vertices_84, vertices_276, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_392, vertices_648, vertices_776, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_162), (true, vertices_276), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_552), (true, vertices_648), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_432) then 22 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 42 3
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 42 682 3
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 52 436 3
cert_coverFacet 3 852
cert_cover_5 3 2 1 3 5 7 84 852 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 8 432 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1750

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1751.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1751

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 166, 682, 820, 468, 932, 632, 904, 848, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 138, 162, 52, 84, 276, 164, 804, 196, 388, 56, 88, 552, 584, 392, 648, 776, 560, 336, 592, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_166, vertices_682, vertices_820, vertices_468, vertices_932, vertices_632, vertices_904, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_138, vertices_162, vertices_52, vertices_84, vertices_276, vertices_164, vertices_804, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_392, vertices_648, vertices_776, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_162), (true, vertices_276), (true, vertices_164), (true, vertices_804), (true, vertices_388), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_804) then 19 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 0 449 1 162 276 164 388 552 648 560 336 592 784 672 896 199 395 93 804 841
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 42 3
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_2 2 1 4 7 8 804
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 42 682 3
cert_coverFacet 2 820
cert_cover_5 2 2 1 3 4 7 52 820 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 932
cert_cover_5 4 2 1 4 6 7 164 932 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1751

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1752.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1752

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 165, 305, 465, 929, 398, 842, 450, 684, 632, 904, 880, 7, 27, 67, 37, 133, 49, 81, 273, 161, 289, 193, 385, 14, 134, 74, 266, 194, 322, 386, 44, 140, 164, 56, 88, 552, 584, 392, 648, 776, 624, 304, 336, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_165, vertices_305, vertices_465, vertices_929, vertices_398, vertices_842, vertices_450, vertices_684, vertices_632, vertices_904, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_74, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_164, vertices_56, vertices_88, vertices_552, vertices_584, vertices_392, vertices_648, vertices_776, vertices_624, vertices_304, vertices_336, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_165), (false, vertices_305), (false, vertices_465), (false, vertices_929), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_140), (true, vertices_552), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_624), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 18 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_624) then 20 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 8 624
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 0 1 2 6 7 398 14 3
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 14 398 3
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 74 842 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 684
cert_cover_5 3 3 1 2 4 6 44 684 3
cert_coverFacet 4 632
cert_cover_5 4 0 2 3 4 5 56 632 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 624 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1752

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1753.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1753

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 678, 682, 820, 468, 900, 632, 904, 848, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 138, 674, 52, 84, 276, 548, 196, 388, 644, 772, 56, 88, 552, 584, 392, 648, 776, 560, 336, 592, 784, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_678, vertices_682, vertices_820, vertices_468, vertices_900, vertices_632, vertices_904, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_138, vertices_674, vertices_52, vertices_84, vertices_276, vertices_548, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_392, vertices_648, vertices_776, vertices_560, vertices_336, vertices_592, vertices_784, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_674), (true, vertices_276), (true, vertices_548), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_674) then 19 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 1 449 0 276 548 388 644 772 552 648 560 336 592 784 896 199 93 395 674 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 6 8 674
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 42 682 3
cert_coverFacet 2 820
cert_cover_5 2 2 1 3 4 7 52 820 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 900
cert_cover_2 4 6 1 7 8 388 900 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1753

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1754.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1754

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 294, 390, 810, 436, 724, 632, 944, 960, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 262, 42, 266, 290, 386, 52, 84, 148, 292, 196, 388, 56, 88, 552, 584, 776, 432, 560, 592, 656, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_294, vertices_390, vertices_810, vertices_436, vertices_724, vertices_632, vertices_944, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_262, vertices_42, vertices_266, vertices_290, vertices_386, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_262), (true, vertices_290), (true, vertices_148), (true, vertices_292), (true, vertices_388), (true, vertices_552), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_656), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_432) then 22 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 294
cert_cover_2 0 1 0 4 7 38 294 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 7 42 810 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 724
cert_cover_5 4 2 1 3 5 6 84 724 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 8 432 944 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1754

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1755.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1755

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 422, 810, 308, 724, 916, 632, 816, 960, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 266, 290, 386, 52, 84, 660, 276, 292, 196, 388, 56, 88, 552, 584, 776, 304, 560, 592, 784, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_422, vertices_810, vertices_308, vertices_724, vertices_916, vertices_632, vertices_816, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_290, vertices_386, vertices_52, vertices_84, vertices_660, vertices_276, vertices_292, vertices_196, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_304, vertices_560, vertices_592, vertices_784, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_290), (true, vertices_660), (true, vertices_276), (true, vertices_292), (true, vertices_388), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 20 16 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_660) then 21 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
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
cert_coverFacet 2 308
cert_cover_2 2 3 1 4 7 52 308 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 660 916 3
cert_coverFacet 5 632
cert_cover_5 5 0 2 3 4 5 56 632 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1755

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1756.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1756

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 422, 810, 436, 724, 632, 816, 912, 960, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 266, 290, 386, 52, 84, 148, 420, 196, 56, 88, 552, 584, 776, 304, 560, 592, 400, 656, 784, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_422, vertices_810, vertices_436, vertices_724, vertices_632, vertices_816, vertices_912, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_290, vertices_386, vertices_52, vertices_84, vertices_148, vertices_420, vertices_196, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_304, vertices_560, vertices_592, vertices_400, vertices_656, vertices_784, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_290), (true, vertices_148), (true, vertices_420), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_420) then 19 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 0 449 1 290 148 552 304 560 592 400 656 784 800 704 896 199 395 93 420 841
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
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 52 436 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1756

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1757.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1757

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 678, 810, 898, 564, 468, 916, 632, 848, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 266, 546, 386, 642, 770, 52, 84, 404, 532, 548, 196, 644, 56, 88, 552, 584, 776, 560, 336, 592, 784, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_678, vertices_810, vertices_898, vertices_564, vertices_468, vertices_916, vertices_632, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_404, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_560, vertices_336, vertices_592, vertices_784, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_404), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_552), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 20 16 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_404) then 21 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 5 8 632 56 3
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
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 468
cert_cover_5 4 1 1 3 5 6 84 468 3
cert_coverFacet 5 916
cert_cover_5 5 1 1 3 6 8 404 916 3
cert_coverFacet 6 632
cert_cover_5 6 0 2 3 4 5 56 632 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1757

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1758.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1758

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 678, 810, 898, 692, 468, 632, 848, 912, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 266, 546, 386, 642, 770, 52, 84, 148, 676, 196, 56, 88, 552, 584, 776, 560, 336, 592, 400, 656, 784, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_678, vertices_810, vertices_898, vertices_692, vertices_468, vertices_632, vertices_848, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_676, vertices_196, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_560, vertices_336, vertices_592, vertices_400, vertices_656, vertices_784, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_148), (true, vertices_676), (true, vertices_552), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_676) then 19 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 0 449 1 546 642 770 148 552 560 336 592 400 656 784 896 199 395 93 676 841
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_2 2 1 4 6 8 676
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 468
cert_cover_5 4 1 1 3 5 6 84 468 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1758

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1759.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1759

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 166, 810, 930, 692, 468, 632, 848, 912, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 266, 162, 802, 386, 52, 84, 148, 164, 196, 56, 88, 552, 584, 776, 560, 336, 592, 400, 656, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_166, vertices_810, vertices_930, vertices_692, vertices_468, vertices_632, vertices_848, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_802, vertices_386, vertices_52, vertices_84, vertices_148, vertices_164, vertices_196, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_560, vertices_336, vertices_592, vertices_400, vertices_656, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_162), (true, vertices_802), (true, vertices_148), (true, vertices_164), (true, vertices_552), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_802) then 19 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 1 449 0 162 148 164 552 560 336 592 400 656 784 672 896 199 93 395 802 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 7 8 802
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 930
cert_cover_5 2 0 0 4 6 7 162 930 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 468
cert_cover_5 4 1 1 3 5 6 84 468 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coverFacet 7 912
cert_cover_2 7 6 3 7 8 400 912 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1759

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1760.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1760

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 93, 841, 449, 166, 810, 930, 692, 852, 452, 900, 632, 7, 11, 131, 29, 69, 73, 265, 193, 321, 385, 38, 134, 42, 266, 162, 802, 386, 52, 84, 532, 164, 196, 324, 388, 644, 772, 56, 88, 552, 584, 776, 560, 592, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_93, vertices_841, vertices_449, vertices_166, vertices_810, vertices_930, vertices_692, vertices_852, vertices_452, vertices_900, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_321, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_802, vertices_386, vertices_52, vertices_84, vertices_532, vertices_164, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_560, vertices_592, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_162), (true, vertices_802), (true, vertices_532), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_552), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_802) then 19 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 1 449 0 162 532 164 324 388 644 772 552 560 592 672 896 199 93 395 802 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 7 8 802
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 930
cert_cover_5 2 0 0 4 6 7 162 930 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 452
cert_cover_2 5 5 1 6 7 196 452 3
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 56 632 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1760

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1761.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1761

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 177, 465, 398, 842, 450, 556, 908, 632, 944, 848, 7, 27, 67, 37, 133, 49, 81, 145, 161, 193, 14, 134, 74, 266, 194, 322, 386, 44, 396, 524, 548, 644, 56, 88, 552, 584, 776, 176, 560, 336, 592, 400, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_177, vertices_465, vertices_398, vertices_842, vertices_450, vertices_556, vertices_908, vertices_632, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_145, vertices_161, vertices_193, vertices_14, vertices_134, vertices_74, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_552, vertices_584, vertices_776, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_177), (false, vertices_465), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_396), (true, vertices_524), (true, vertices_552), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_396) then 19 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 74 842 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 908
cert_cover_5 4 0 1 2 6 8 396 908 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1761

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1762.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1762

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 421, 305, 849, 449, 654, 842, 450, 898, 684, 632, 944, 7, 27, 67, 37, 133, 49, 81, 273, 289, 193, 321, 385, 14, 134, 74, 522, 194, 322, 386, 642, 770, 44, 652, 164, 56, 88, 552, 584, 304, 560, 592, 784, 416, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_421, vertices_305, vertices_849, vertices_449, vertices_654, vertices_842, vertices_450, vertices_898, vertices_684, vertices_632, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_273, vertices_289, vertices_193, vertices_321, vertices_385, vertices_14, vertices_134, vertices_74, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_44, vertices_652, vertices_164, vertices_56, vertices_88, vertices_552, vertices_584, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_421), (false, vertices_305), (false, vertices_849), (false, vertices_449), (true, vertices_522), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_652), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_849) then 21 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_652) then 18 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
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
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 74 842 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 684
cert_cover_5 4 0 1 2 4 6 44 684 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1762

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1763.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1763

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 523, 899, 93, 841, 449, 166, 682, 436, 852, 452, 632, 944, 7, 11, 131, 515, 29, 69, 73, 521, 193, 321, 385, 769, 38, 134, 42, 522, 162, 642, 52, 84, 276, 164, 196, 324, 388, 56, 88, 552, 584, 432, 560, 592, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_523, vertices_899, vertices_93, vertices_841, vertices_449, vertices_166, vertices_682, vertices_436, vertices_852, vertices_452, vertices_632, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_29, vertices_69, vertices_73, vertices_521, vertices_193, vertices_321, vertices_385, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_162, vertices_642, vertices_52, vertices_84, vertices_276, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_523), (false, vertices_899), (false, vertices_93), (false, vertices_841), (false, vertices_449), (true, vertices_162), (true, vertices_276), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_552), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_432) then 21 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 42 3
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 42 682 3
cert_coverFacet 2 436
cert_cover_5 2 1 1 3 4 6 52 436 3
cert_coverFacet 3 852
cert_cover_5 3 2 1 3 5 7 84 852 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 56 632 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1763

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1764.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1764

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 165, 305, 465, 929, 526, 902, 842, 450, 684, 632, 880, 7, 27, 67, 37, 133, 49, 81, 273, 161, 289, 193, 385, 14, 134, 518, 74, 522, 194, 322, 386, 770, 44, 524, 164, 644, 56, 88, 552, 584, 624, 304, 336, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_165, vertices_305, vertices_465, vertices_929, vertices_526, vertices_902, vertices_842, vertices_450, vertices_684, vertices_632, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_518, vertices_74, vertices_522, vertices_194, vertices_322, vertices_386, vertices_770, vertices_44, vertices_524, vertices_164, vertices_644, vertices_56, vertices_88, vertices_552, vertices_584, vertices_624, vertices_304, vertices_336, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_165), (false, vertices_305), (false, vertices_465), (false, vertices_929), (true, vertices_518), (true, vertices_522), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_524), (true, vertices_644), (true, vertices_552), (true, vertices_584), (true, vertices_624), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 18 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_624) then 20 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 8 624
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 1 2 4 6 8 684 44 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 2 0 1 6 7 134 902 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 684
cert_cover_5 4 3 1 2 4 6 44 684 3
cert_coverFacet 5 632
cert_cover_5 5 0 2 3 4 5 56 632 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 624 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1764

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1765.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1765

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 841, 449, 897, 550, 646, 810, 692, 468, 376, 944, 7, 11, 131, 29, 69, 73, 521, 193, 321, 385, 641, 769, 38, 134, 518, 42, 522, 546, 642, 52, 84, 148, 548, 196, 644, 56, 88, 296, 328, 776, 688, 304, 336, 400, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_841, vertices_449, vertices_897, vertices_550, vertices_646, vertices_810, vertices_692, vertices_468, vertices_376, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_521, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_518, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_148, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_688, vertices_304, vertices_336, vertices_400, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_841), (false, vertices_449), (false, vertices_897), (true, vertices_518), (true, vertices_546), (true, vertices_148), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_688), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_688) then 21 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 3 4 6 8 688
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 550
cert_cover_2 0 1 0 4 8 38 550 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 810
cert_cover_5 2 0 0 2 4 7 42 810 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 84 468 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 688 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1765

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1766.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1766

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 841, 449, 897, 678, 810, 692, 468, 376, 816, 912, 7, 11, 131, 29, 69, 73, 521, 193, 321, 385, 641, 769, 38, 134, 42, 522, 546, 642, 52, 84, 148, 676, 196, 56, 88, 296, 328, 776, 304, 560, 336, 400, 656, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_841, vertices_449, vertices_897, vertices_678, vertices_810, vertices_692, vertices_468, vertices_376, vertices_816, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_521, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_148, vertices_676, vertices_196, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_400, vertices_656, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_841), (false, vertices_449), (false, vertices_897), (true, vertices_546), (true, vertices_148), (true, vertices_676), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_676) then 18 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
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
cert_coverFacet 2 692
cert_cover_5 2 1 1 3 4 6 52 692 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1766

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1767.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1767

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 841, 449, 897, 678, 810, 564, 468, 916, 376, 816, 7, 11, 131, 29, 69, 73, 521, 193, 321, 385, 641, 769, 38, 134, 42, 522, 546, 642, 52, 84, 404, 532, 548, 196, 644, 56, 88, 296, 328, 776, 304, 560, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_841, vertices_449, vertices_897, vertices_678, vertices_810, vertices_564, vertices_468, vertices_916, vertices_376, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_521, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_404, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_841), (false, vertices_449), (false, vertices_897), (true, vertices_546), (true, vertices_404), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 19 15 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_404) then 20 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
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
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 8 404 916 3
cert_coverFacet 5 376
cert_cover_5 5 0 2 3 4 5 56 376 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1767

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1768.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1768

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 139, 421, 681, 94, 842, 906, 450, 308, 852, 452, 632, 944, 7, 11, 131, 37, 133, 41, 137, 161, 30, 70, 74, 138, 778, 194, 322, 386, 52, 84, 276, 292, 196, 324, 388, 56, 88, 552, 584, 648, 304, 560, 592, 784, 416, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_139, vertices_421, vertices_681, vertices_94, vertices_842, vertices_906, vertices_450, vertices_308, vertices_852, vertices_452, vertices_632, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_37, vertices_133, vertices_41, vertices_137, vertices_161, vertices_30, vertices_70, vertices_74, vertices_138, vertices_778, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_276, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_552, vertices_584, vertices_648, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_139), (false, vertices_421), (false, vertices_681), (true, vertices_74), (true, vertices_778), (true, vertices_322), (true, vertices_386), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_88), (true, vertices_584), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 20 else
  if p.val = (false, vertices_199) then 17 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_448) then 13 else
  if p.val = (true, vertices_832) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
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
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 852
cert_cover_5 5 2 1 3 5 7 84 852 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 632
cert_cover_5 7 1 2 3 4 5 56 632 3
cert_coverFacet 8 944
cert_cover_5 8 0 3 4 6 7 304 944 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 5 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1768

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1769.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1769

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 526, 646, 458, 650, 812, 376, 904, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 518, 74, 138, 522, 194, 642, 44, 524, 548, 644, 56, 88, 296, 328, 392, 648, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_526, vertices_646, vertices_458, vertices_650, vertices_812, vertices_376, vertices_904, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_518, vertices_74, vertices_138, vertices_522, vertices_194, vertices_642, vertices_44, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_642), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 458
cert_cover_5 2 0 0 2 5 6 74 458 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 44 812 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 976
cert_cover_5 7 1 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1769

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1771.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1771

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 298, 778, 802, 820, 724, 376, 904, 976, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 266, 522, 290, 546, 642, 770, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 392, 648, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_298, vertices_778, vertices_802, vertices_820, vertices_724, vertices_376, vertices_904, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_266, vertices_522, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_266), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_720) then 23 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 724
cert_cover_5 5 1 1 3 5 6 84 724 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coverFacet 8 976
cert_cover_5 8 1 3 5 6 7 720 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1771

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1772.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1772

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 451, 549, 369, 929, 206, 812, 652, 312, 728, 792, 976, 7, 27, 67, 131, 37, 517, 49, 81, 289, 545, 321, 385, 641, 14, 134, 74, 194, 44, 140, 524, 548, 644, 56, 88, 280, 536, 296, 200, 648, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_451, vertices_549, vertices_369, vertices_929, vertices_206, vertices_812, vertices_652, vertices_312, vertices_728, vertices_792, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_14, vertices_134, vertices_74, vertices_194, vertices_44, vertices_140, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_200, vertices_648, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_451), (false, vertices_549), (false, vertices_369), (false, vertices_929), (true, vertices_140), (true, vertices_524), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_200), (true, vertices_648), (true, vertices_776), (true, vertices_720), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 10 16 17 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_369) then 18 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_720) then 19 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_rows_3
cert_pivot_3 0 3 1
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 812
cert_cover_5 1 2 1 2 4 7 44 812 3
cert_coverFacet 2 652
cert_cover_2 2 2 1 6 8 140 652 3
cert_coverFacet 3 312
cert_cover_2 3 3 2 4 7 56 312 3
cert_coverFacet 4 728
cert_cover_5 4 0 2 3 5 6 88 728 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1772

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1774.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1774

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 166, 810, 674, 692, 852, 964, 376, 904, 816, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 162, 546, 642, 52, 84, 532, 164, 196, 836, 644, 56, 88, 296, 328, 392, 648, 776, 304, 560, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_166, vertices_810, vertices_674, vertices_692, vertices_852, vertices_964, vertices_376, vertices_904, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_162, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_164, vertices_196, vertices_836, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_162), (true, vertices_546), (true, vertices_532), (true, vertices_164), (true, vertices_836), (true, vertices_644), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_162) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_836) then 20 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_2 2 1 5 7 8 836
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 964
cert_cover_5 5 2 1 5 6 7 196 964 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1774

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1775.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1775

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 166, 810, 674, 820, 724, 676, 376, 904, 976, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 162, 546, 642, 52, 84, 532, 164, 548, 196, 644, 56, 88, 296, 328, 392, 648, 776, 304, 720, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_166, vertices_810, vertices_674, vertices_820, vertices_724, vertices_676, vertices_376, vertices_904, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_162, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_164, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_162), (true, vertices_546), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_162) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_720) then 23 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 42 810 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 724
cert_cover_5 4 0 1 3 5 6 84 724 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coverFacet 8 976
cert_cover_5 8 0 3 5 6 7 720 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1775

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1776.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1776

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 93, 457, 678, 810, 308, 724, 788, 804, 376, 904, 976, 7, 11, 131, 29, 69, 73, 137, 193, 38, 134, 42, 522, 546, 642, 52, 84, 276, 532, 292, 548, 196, 644, 772, 56, 88, 296, 328, 392, 648, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_93, vertices_457, vertices_678, vertices_810, vertices_308, vertices_724, vertices_788, vertices_804, vertices_376, vertices_904, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_29, vertices_69, vertices_73, vertices_137, vertices_193, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_196, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_296), (true, vertices_776), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_720) then 23 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 308
cert_cover_2 2 3 1 4 7 52 308 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coverFacet 8 976
cert_cover_5 8 1 3 5 6 7 720 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1776

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1778.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1778

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 387, 93, 457, 678, 554, 898, 372, 484, 568, 856, 944, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 522, 546, 386, 642, 770, 52, 84, 356, 164, 196, 56, 88, 536, 552, 328, 776, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_387, vertices_93, vertices_457, vertices_678, vertices_554, vertices_898, vertices_372, vertices_484, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_387), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_642), (true, vertices_356), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_356) then 19 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 0 387 1 546 642 164 536 552 304 560 336 784 416 672 896 199 779 93 356 457
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
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 52 372 3
cert_coverFacet 4 484
cert_cover_5 4 1 1 4 5 6 356 484 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 88 856 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1778

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1779.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1779

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 387, 93, 457, 678, 554, 898, 820, 724, 376, 808, 976, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 522, 546, 386, 642, 770, 52, 84, 532, 548, 196, 644, 56, 88, 296, 552, 328, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_387, vertices_93, vertices_457, vertices_678, vertices_554, vertices_898, vertices_820, vertices_724, vertices_376, vertices_808, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_387), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_642), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_552), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_720) then 22 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 976
cert_cover_5 7 1 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1779

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1780.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1780

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 387, 93, 457, 422, 554, 802, 692, 724, 568, 856, 992, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 522, 290, 546, 386, 770, 52, 84, 660, 164, 196, 56, 88, 536, 552, 328, 776, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_387, vertices_93, vertices_457, vertices_422, vertices_554, vertices_802, vertices_692, vertices_724, vertices_568, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_290, vertices_546, vertices_386, vertices_770, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_387), (false, vertices_93), (false, vertices_457), (true, vertices_290), (true, vertices_546), (true, vertices_660), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 20 16 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_660) then 21 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 38 3
cert_row_2 1 1 3 6 8 660
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 38 422 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 6 84 724 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 88 856 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1780

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1781.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1781

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 526, 646, 458, 778, 898, 812, 376, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 518, 74, 266, 522, 194, 386, 642, 770, 44, 524, 548, 644, 56, 88, 296, 328, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_526, vertices_646, vertices_458, vertices_778, vertices_898, vertices_812, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_518, vertices_74, vertices_266, vertices_522, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_776), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 458
cert_cover_5 2 0 0 2 5 6 74 458 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 812
cert_cover_5 5 2 1 2 4 7 44 812 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 976
cert_cover_5 7 1 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1781

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1782.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1782

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 270, 646, 774, 458, 898, 812, 376, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 262, 518, 74, 266, 194, 386, 642, 770, 44, 268, 548, 644, 772, 56, 88, 296, 328, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_270, vertices_646, vertices_774, vertices_458, vertices_898, vertices_812, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_262, vertices_518, vertices_74, vertices_266, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_268), (true, vertices_772), (true, vertices_296), (true, vertices_328), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 7 458 74 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 458
cert_cover_5 3 0 0 2 5 6 74 458 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 812
cert_cover_5 5 2 1 2 4 7 44 812 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 976
cert_cover_5 7 1 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1782

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1890 : Certifies 1890 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1750.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1891 : Certifies 1891 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1751.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1892 : Certifies 1892 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1752.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1893 : Certifies 1893 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1753.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1894 : Certifies 1894 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1754.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1895 : Certifies 1895 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1755.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1896 : Certifies 1896 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1756.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1897 : Certifies 1897 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1757.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1898 : Certifies 1898 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1758.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1899 : Certifies 1899 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1759.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1900 : Certifies 1900 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1760.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1901 : Certifies 1901 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1761.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1902 : Certifies 1902 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1762.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1903 : Certifies 1903 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1763.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1904 : Certifies 1904 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1764.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1905 : Certifies 1905 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1765.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1906 : Certifies 1906 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1766.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1907 : Certifies 1907 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1767.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1908 : Certifies 1908 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1768.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1909 : Certifies 1909 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1769.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1910 : Certifies 1910 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1771.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1911 : Certifies 1911 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1772.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1912 : Certifies 1912 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1774.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1913 : Certifies 1913 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1775.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1914 : Certifies 1914 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1776.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1915 : Certifies 1915 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1778.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1916 : Certifies 1916 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1779.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1917 : Certifies 1917 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1780.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1918 : Certifies 1918 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1781.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1919 : Certifies 1919 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1782.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B063 (j : Fin 30) :
    Certifies (1890 + j.val) := by
  fin_cases j
  · exact projection_1890
  · exact projection_1891
  · exact projection_1892
  · exact projection_1893
  · exact projection_1894
  · exact projection_1895
  · exact projection_1896
  · exact projection_1897
  · exact projection_1898
  · exact projection_1899
  · exact projection_1900
  · exact projection_1901
  · exact projection_1902
  · exact projection_1903
  · exact projection_1904
  · exact projection_1905
  · exact projection_1906
  · exact projection_1907
  · exact projection_1908
  · exact projection_1909
  · exact projection_1910
  · exact projection_1911
  · exact projection_1912
  · exact projection_1913
  · exact projection_1914
  · exact projection_1915
  · exact projection_1916
  · exact projection_1917
  · exact projection_1918
  · exact projection_1919

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
