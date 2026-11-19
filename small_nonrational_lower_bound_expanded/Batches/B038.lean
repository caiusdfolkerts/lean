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
/- Source: ProjectionCertificates/R_one_six_0755.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0755

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 449, 270, 906, 812, 820, 744, 624, 976, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 266, 386, 44, 268, 52, 276, 804, 104, 552, 200, 648, 776, 112, 560, 336, 592, 784, 608, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_449, vertices_270, vertices_906, vertices_812, vertices_820, vertices_744, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_804, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_608, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_449), (true, vertices_266), (true, vertices_268), (true, vertices_804), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_804) then 17 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 336 976 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0755

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0756.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0756

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 270, 906, 812, 820, 744, 624, 848, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 266, 386, 44, 268, 52, 276, 804, 104, 552, 200, 648, 776, 112, 560, 336, 592, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_270, vertices_906, vertices_812, vertices_820, vertices_744, vertices_624, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_804, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_266), (true, vertices_268), (true, vertices_804), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_804) then 14 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
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
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0756

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0757.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0757

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 270, 906, 812, 564, 744, 752, 912, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 560, 208, 400, 656, 784, 736, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_270, vertices_906, vertices_812, vertices_564, vertices_744, vertices_752, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_400, vertices_656, vertices_784, vertices_736, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_656), (true, vertices_736), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 14 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 18 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_736) then 20 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
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
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_rows_3
cert_pivot_3 0 5 1
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 744
cert_cover_5 4 0 2 4 5 6 104 744 3
cert_coverFacet 5 752
cert_cover_5 5 0 3 4 5 6 112 752 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0757

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0758.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0758

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 526, 774, 906, 556, 628, 744, 976, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 518, 138, 522, 386, 770, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_526, vertices_774, vertices_906, vertices_556, vertices_628, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_518), (true, vertices_522), (true, vertices_770), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_592), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
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
cert_row_2 1 3 5 6 7 464
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 906
cert_cover_5 2 0 0 2 6 7 138 906 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 628
cert_cover_5 4 2 1 3 4 5 52 628 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 8 464 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0758

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0759.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0759

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 526, 774, 906, 556, 820, 744, 880, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 518, 138, 522, 386, 770, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 816, 336, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_526, vertices_774, vertices_906, vertices_556, vertices_820, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_816, vertices_336, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_518), (true, vertices_522), (true, vertices_770), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_816), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 14 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_608) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_rows_3
cert_pivot_3 0 3 2
cert_heightProof 3
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 906
cert_cover_5 2 1 0 2 6 7 138 906 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0759

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0760.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0760

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 526, 774, 906, 620, 564, 968, 880, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 518, 138, 522, 386, 770, 44, 524, 52, 532, 548, 772, 104, 200, 584, 904, 112, 560, 336, 784, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_526, vertices_774, vertices_906, vertices_620, vertices_564, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_904, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_518), (true, vertices_522), (true, vertices_770), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_904), (true, vertices_560), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 18 14 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_904) then 19 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_904), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 6 7 8 904
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 3 4 5 7 8 880 112 3
cert_rows_3
cert_pivot_3 1 6 3
cert_heightProof 3
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 906
cert_cover_5 2 0 0 2 6 7 138 906 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 44 620 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 968
cert_cover_5 5 0 2 5 6 7 200 968 3
cert_coverFacet 6 880
cert_cover_5 6 2 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0760

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0761.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0761

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 277, 121, 465, 782, 906, 620, 820, 712, 368, 992, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 548, 772, 104, 200, 584, 648, 112, 304, 336, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_277, vertices_121, vertices_465, vertices_782, vertices_906, vertices_620, vertices_820, vertices_712, vertices_368, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_336, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_584), (true, vertices_648), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 12 21 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_778) then 20 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 712
cert_cover_2 4 5 2 6 8 200 712 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 352 992 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0761

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0762.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0762

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 277, 121, 465, 782, 906, 620, 820, 712, 752, 912, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 548, 772, 104, 200, 584, 648, 112, 560, 208, 400, 656, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_277, vertices_121, vertices_465, vertices_782, vertices_906, vertices_620, vertices_820, vertices_712, vertices_752, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_560, vertices_208, vertices_400, vertices_656, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_656), (true, vertices_784), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 12 21 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_778) then 20 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 712
cert_cover_2 4 5 2 6 8 200 712 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0762

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0763.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0763

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 277, 121, 209, 913, 782, 906, 620, 820, 712, 752, 7, 11, 131, 21, 261, 57, 73, 81, 145, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 548, 772, 104, 200, 584, 648, 112, 560, 208, 656, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_277, vertices_121, vertices_209, vertices_913, vertices_782, vertices_906, vertices_620, vertices_820, vertices_712, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_145, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_560, vertices_208, vertices_656, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_209), (false, vertices_913), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 10 19 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (false, vertices_913) then 15 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 712
cert_cover_2 4 5 2 6 8 200 712 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0763

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0764.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0764

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 620, 564, 712, 880, 960, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 200, 584, 648, 112, 560, 336, 784, 608, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_620, vertices_564, vertices_712, vertices_880, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_608), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 9 19 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_789) then 11 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_465) then 15 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_584) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_832) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 3 4 5 7 8 880 112 3
cert_rows_3
cert_pivot_3 1 0 3
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 712
cert_cover_2 4 5 2 6 8 200 712 3
cert_coverFacet 5 880
cert_cover_5 5 2 3 4 5 7 112 880 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0764

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0765.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0765

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 620, 564, 712, 752, 912, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 200, 584, 648, 112, 560, 208, 400, 656, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_620, vertices_564, vertices_712, vertices_752, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_560, vertices_208, vertices_400, vertices_656, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_656), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 9 19 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_789) then 11 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_465) then 15 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_584) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 3 4 5 6 8 752 112 3
cert_rows_3
cert_pivot_3 1 0 3
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 712
cert_cover_2 4 5 2 6 8 200 712 3
cert_coverFacet 5 752
cert_cover_5 5 2 3 4 5 6 112 752 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0765

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0766.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0766

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 209, 401, 782, 906, 556, 628, 744, 976, 7, 11, 131, 21, 261, 57, 73, 81, 145, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 208, 592, 400, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_209, vertices_401, vertices_782, vertices_906, vertices_556, vertices_628, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_145, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_208, vertices_592, vertices_400, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_209), (false, vertices_401), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_592), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 10 19 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_789) then 12 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
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
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0766

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0767.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0767

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 449, 782, 906, 556, 820, 744, 624, 976, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 560, 336, 592, 784, 608, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_449, vertices_782, vertices_906, vertices_556, vertices_820, vertices_744, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_608, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_449), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 12 21 15 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_778) then 20 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
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
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 336 976 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0767

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0768.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0768

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 337, 449, 782, 906, 556, 628, 744, 976, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 321, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 336, 592, 784, 608, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_337, vertices_449, vertices_782, vertices_906, vertices_556, vertices_628, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_608, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_337), (false, vertices_449), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_592), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 10 19 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_789) then 12 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
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
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 336 976 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0768

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0769.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0769

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 556, 628, 744, 848, 960, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 336, 592, 784, 608, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_556, vertices_628, vertices_744, vertices_848, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_592), (true, vertices_608), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 9 19 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_789) then 11 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_465) then 15 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_832) then 7 else
  if p.val = (true, vertices_896) then 8 else
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
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
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
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0769

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0770.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0770

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 556, 564, 744, 880, 960, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 560, 336, 784, 608, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_556, vertices_564, vertices_744, vertices_880, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_608), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 9 19 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_789) then 11 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_465) then 15 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_832) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 2 4 5 6 8 744 104 3
cert_row_4 2 3 4 5 7 8 880 112 3
cert_rows_3
cert_pivot_3 2 0 3
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 744
cert_cover_5 4 1 2 4 5 6 104 744 3
cert_coverFacet 5 880
cert_cover_5 5 2 3 4 5 7 112 880 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0770

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0771.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0771

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 556, 628, 744, 720, 912, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 208, 592, 400, 656, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_556, vertices_628, vertices_744, vertices_720, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_592), (true, vertices_656), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 9 19 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_789) then 11 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_465) then 15 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_656) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
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
cert_coverFacet 5 720
cert_cover_2 5 5 3 6 8 208 720 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0771

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0772.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0772

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 782, 906, 556, 820, 744, 624, 848, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 560, 336, 592, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_782, vertices_906, vertices_556, vertices_820, vertices_744, vertices_624, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 9 18 12 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_341) then 11 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_778) then 17 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 7 8 820 52 3
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
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0772

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0773.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0773

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 782, 906, 556, 820, 744, 368, 864, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 304, 336, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_782, vertices_906, vertices_556, vertices_820, vertices_744, vertices_368, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 9 18 12 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_341) then 11 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_778) then 17 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 7 8 820 52 3
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
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0773

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0774.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0774

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 782, 906, 556, 308, 804, 744, 880, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 292, 548, 772, 104, 552, 200, 648, 112, 304, 336, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_782, vertices_906, vertices_556, vertices_308, vertices_804, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_778), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 9 18 12 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_341) then 11 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_778) then 17 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 2 4 5 6 8 744 104 3
cert_row_4 2 3 4 5 7 8 880 112 3
cert_rows_3
cert_pivot_3 2 0 3
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 804
cert_cover_2 4 4 1 7 8 292 804 3
cert_coverFacet 5 744
cert_cover_5 5 1 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 2 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0774

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0775.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0775

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 782, 906, 556, 564, 788, 744, 880, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 532, 548, 772, 104, 552, 200, 648, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_782, vertices_906, vertices_556, vertices_564, vertices_788, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_778), (true, vertices_524), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 9 18 12 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_341) then 11 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_778) then 17 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 2 4 5 6 8 744 104 3
cert_row_4 2 3 4 5 7 8 880 112 3
cert_rows_3
cert_pivot_3 2 0 3
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 744
cert_cover_5 5 1 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 2 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0775

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0776.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0776

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 449, 782, 906, 556, 820, 744, 496, 928, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 548, 772, 104, 552, 200, 648, 112, 304, 336, 224, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_449, vertices_782, vertices_906, vertices_556, vertices_820, vertices_744, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_449), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 12 21 15 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_778) then 20 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
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
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0776

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0777.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0777

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 782, 906, 556, 564, 744, 240, 944, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 552, 200, 648, 112, 176, 560, 208, 400, 784, 224, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_556, vertices_564, vertices_744, vertices_240, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_400, vertices_784, vertices_224, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 9 19 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_789) then 11 else
  if p.val = (false, vertices_121) then 14 else
  if p.val = (false, vertices_465) then 15 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_648) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 2 4 5 6 8 744 104 3
cert_row_4 2 3 4 6 7 8 944 176 3
cert_rows_3
cert_pivot_3 2 0 3
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 744
cert_cover_5 4 1 2 4 5 6 104 744 3
cert_coverFacet 5 240
cert_cover_2 5 4 3 5 6 112 240 3
cert_coverFacet 6 944
cert_cover_5 6 2 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0777

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0778.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0778

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 398, 412, 212, 376, 976, 864, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 266, 386, 28, 396, 84, 148, 196, 56, 280, 296, 112, 208, 336, 400, 352, 608, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_398, vertices_412, vertices_212, vertices_376, vertices_976, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_28, vertices_396, vertices_84, vertices_148, vertices_196, vertices_56, vertices_280, vertices_296, vertices_112, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_396), (true, vertices_148), (true, vertices_280), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 17 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 10 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_737) then 19 else
  if p.val = (true, vertices_396) then 14 else
  if p.val = (true, vertices_148) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_208) then 3 else
  if p.val = (true, vertices_336) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_832) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 2 3 4 5 7 376 56 3
cert_row_4 2 3 5 6 7 8 976 208 3
cert_rows_3
cert_pivot_3 2 1 3
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 412
cert_cover_5 1 0 1 2 3 6 28 412 3
cert_coverFacet 2 212
cert_cover_2 2 3 1 5 6 84 212 3
cert_coverFacet 3 376
cert_cover_5 3 1 2 3 4 5 56 376 3
cert_coverFacet 4 976
cert_cover_5 4 2 3 5 6 7 208 976 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0778

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0779.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0779

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 398, 412, 212, 632, 792, 976, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 266, 386, 28, 396, 84, 148, 196, 56, 280, 536, 552, 776, 112, 208, 592, 400, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_398, vertices_412, vertices_212, vertices_632, vertices_792, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_28, vertices_396, vertices_84, vertices_148, vertices_196, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_112, vertices_208, vertices_592, vertices_400, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_396), (true, vertices_148), (true, vertices_280), (true, vertices_536), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 17 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 10 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_737) then 19 else
  if p.val = (true, vertices_396) then 14 else
  if p.val = (true, vertices_148) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_208) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 2 3 4 5 8 632 56 3
cert_row_4 2 3 5 6 7 8 976 208 3
cert_rows_3
cert_pivot_3 2 1 3
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 412
cert_cover_5 1 0 1 2 3 6 28 412 3
cert_coverFacet 2 212
cert_cover_2 2 3 1 5 6 84 212 3
cert_coverFacet 3 632
cert_cover_5 3 1 2 3 4 5 56 632 3
cert_coverFacet 4 792
cert_cover_2 4 3 2 7 8 280 792 3
cert_coverFacet 5 976
cert_cover_5 5 2 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0779

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0780.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0780

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 405, 121, 721, 270, 906, 812, 308, 744, 880, 912, 7, 11, 131, 21, 389, 57, 73, 81, 145, 193, 14, 262, 138, 266, 386, 44, 268, 52, 276, 292, 104, 552, 200, 648, 776, 112, 304, 592, 400, 656, 784, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_405, vertices_121, vertices_721, vertices_270, vertices_906, vertices_812, vertices_308, vertices_744, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_389, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_304, vertices_592, vertices_400, vertices_656, vertices_784, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_405), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_292), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_784), (true, vertices_608), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_59 0 266 1 268 2 292 552 648 776 304 784 608 800 896 203 391 405 63 121 721
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
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0780

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0781.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0781

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 405, 121, 721, 270, 906, 812, 628, 788, 744, 912, 7, 11, 131, 21, 389, 57, 73, 81, 145, 193, 14, 262, 138, 266, 386, 44, 268, 52, 276, 532, 548, 772, 104, 552, 200, 648, 776, 112, 592, 400, 656, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_405, vertices_121, vertices_721, vertices_270, vertices_906, vertices_812, vertices_628, vertices_788, vertices_744, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_389, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_400, vertices_656, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_405), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_784), (true, vertices_608), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
cert_nodeAtPriority_59 0 266 1 268 2 532 548 772 552 648 776 784 608 896 203 391 405 63 121 721
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
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0781

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0791.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0791

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 681, 737, 78, 330, 962, 348, 568, 920, 880, 7, 11, 131, 53, 69, 41, 137, 97, 673, 193, 14, 70, 74, 266, 194, 322, 386, 28, 76, 84, 56, 280, 536, 552, 328, 392, 648, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_681, vertices_737, vertices_78, vertices_330, vertices_962, vertices_348, vertices_568, vertices_920, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_673, vertices_193, vertices_14, vertices_70, vertices_74, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_76, vertices_84, vertices_56, vertices_280, vertices_536, vertices_552, vertices_328, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_681), (false, vertices_737), (true, vertices_74), (true, vertices_322), (true, vertices_76), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 19 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
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
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 1 2 3 5 7 348 28 3
cert_row_4 2 2 3 6 7 8 920 280 2
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 348
cert_cover_5 3 1 1 2 3 5 28 348 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 920
cert_cover_5 5 2 2 3 6 7 280 920 2
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0791

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0792.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0792

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 169, 737, 78, 330, 962, 348, 696, 920, 880, 7, 11, 131, 53, 69, 41, 137, 97, 161, 193, 14, 70, 74, 266, 194, 322, 386, 28, 76, 84, 56, 664, 280, 168, 328, 392, 112, 560, 336, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_169, vertices_737, vertices_78, vertices_330, vertices_962, vertices_348, vertices_696, vertices_920, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_74, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_76, vertices_84, vertices_56, vertices_664, vertices_280, vertices_168, vertices_328, vertices_392, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_169), (false, vertices_737), (true, vertices_74), (true, vertices_322), (true, vertices_76), (true, vertices_664), (true, vertices_280), (true, vertices_328), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_664) then 18 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
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
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
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
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 2 3 5 7 348 28 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 348
cert_cover_5 3 2 1 2 3 5 28 348 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 920
cert_cover_5 5 1 2 3 6 7 664 920 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0792

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0793.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0793

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 451, 341, 553, 561, 913, 206, 124, 488, 936, 880, 7, 11, 67, 131, 21, 69, 41, 521, 49, 273, 529, 545, 321, 385, 641, 14, 70, 138, 194, 60, 76, 84, 104, 424, 552, 200, 648, 112, 560, 336, 784, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_451, vertices_341, vertices_553, vertices_561, vertices_913, vertices_206, vertices_124, vertices_488, vertices_936, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_273, vertices_529, vertices_545, vertices_321, vertices_385, vertices_641, vertices_14, vertices_70, vertices_138, vertices_194, vertices_60, vertices_76, vertices_84, vertices_104, vertices_424, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_451), (false, vertices_341), (false, vertices_553), (false, vertices_561), (false, vertices_913), (true, vertices_76), (true, vertices_104), (true, vertices_424), (true, vertices_200), (true, vertices_112), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_451) then 11 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_561) then 2 else
  if p.val = (false, vertices_913) then 18 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_424) then 16 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 2 4 6 7 424
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 6 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 124
cert_cover_5 1 2 1 2 3 5 60 124 3
cert_coverFacet 2 488
cert_cover_5 2 1 2 4 5 6 104 488 3
cert_coverFacet 3 936
cert_cover_5 3 1 2 4 6 8 424 936 3
cert_coverFacet 4 880
cert_cover_5 4 3 3 4 5 7 112 880 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0793

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1140 : Certifies 1140 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0755.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1141 : Certifies 1141 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0756.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1142 : Certifies 1142 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0757.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1143 : Certifies 1143 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0758.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1144 : Certifies 1144 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0759.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1145 : Certifies 1145 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0760.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1146 : Certifies 1146 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0761.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1147 : Certifies 1147 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0762.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1148 : Certifies 1148 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0763.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1149 : Certifies 1149 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0764.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1150 : Certifies 1150 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0765.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1151 : Certifies 1151 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0766.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1152 : Certifies 1152 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0767.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1153 : Certifies 1153 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0768.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1154 : Certifies 1154 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0769.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1155 : Certifies 1155 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0770.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1156 : Certifies 1156 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0771.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1157 : Certifies 1157 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0772.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1158 : Certifies 1158 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0773.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1159 : Certifies 1159 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0774.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1160 : Certifies 1160 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0775.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1161 : Certifies 1161 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0776.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1162 : Certifies 1162 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0777.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1163 : Certifies 1163 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0778.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1164 : Certifies 1164 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0779.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1165 : Certifies 1165 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0780.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1166 : Certifies 1166 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0781.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1167 : Certifies 1167 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0791.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1168 : Certifies 1168 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0792.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1169 : Certifies 1169 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0793.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B038 (j : Fin 30) :
    Certifies (1140 + j.val) := by
  fin_cases j
  · exact projection_1140
  · exact projection_1141
  · exact projection_1142
  · exact projection_1143
  · exact projection_1144
  · exact projection_1145
  · exact projection_1146
  · exact projection_1147
  · exact projection_1148
  · exact projection_1149
  · exact projection_1150
  · exact projection_1151
  · exact projection_1152
  · exact projection_1153
  · exact projection_1154
  · exact projection_1155
  · exact projection_1156
  · exact projection_1157
  · exact projection_1158
  · exact projection_1159
  · exact projection_1160
  · exact projection_1161
  · exact projection_1162
  · exact projection_1163
  · exact projection_1164
  · exact projection_1165
  · exact projection_1166
  · exact projection_1167
  · exact projection_1168
  · exact projection_1169

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
