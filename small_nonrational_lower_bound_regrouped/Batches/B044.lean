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
/- Source: ProjectionCertificates/R_one_six_1020.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 214, 122, 202, 300, 564, 724, 804, 488, 880, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 134, 58, 74, 138, 82, 194, 44, 268, 52, 212, 532, 292, 548, 644, 772, 104, 296, 200, 392, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_214, vertices_122, vertices_202, vertices_300, vertices_564, vertices_724, vertices_804, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_268, vertices_52, vertices_212, vertices_532, vertices_292, vertices_548, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_212), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
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
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
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
cert_row_2 1 1 3 5 6 212
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 724
cert_cover_5 5 1 1 3 5 8 212 724 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 488
cert_cover_5 7 2 2 4 5 6 104 488 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1020

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1021.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1021

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 214, 122, 202, 556, 564, 724, 488, 808, 880, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 134, 58, 74, 138, 82, 194, 44, 524, 52, 212, 532, 548, 644, 104, 296, 552, 200, 392, 776, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_214, vertices_122, vertices_202, vertices_556, vertices_564, vertices_724, vertices_488, vertices_808, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_524, vertices_52, vertices_212, vertices_532, vertices_548, vertices_644, vertices_104, vertices_296, vertices_552, vertices_200, vertices_392, vertices_776, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_212), (true, vertices_532), (true, vertices_548), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_200), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
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
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
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
cert_row_2 1 1 3 5 6 212
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 724
cert_cover_5 5 1 1 3 5 8 212 724 3
cert_coverFacet 6 488
cert_cover_5 6 2 2 4 5 6 104 488 3
cert_coverFacet 7 808
cert_cover_2 7 4 2 7 8 296 808 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1021

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1022.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 523, 771, 117, 197, 809, 481, 654, 962, 220, 568, 728, 880, 7, 11, 259, 515, 53, 69, 133, 41, 521, 97, 289, 193, 385, 769, 14, 134, 522, 386, 642, 770, 28, 140, 84, 196, 56, 216, 536, 552, 648, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_523, vertices_771, vertices_117, vertices_197, vertices_809, vertices_481, vertices_654, vertices_962, vertices_220, vertices_568, vertices_728, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_53, vertices_69, vertices_133, vertices_41, vertices_521, vertices_97, vertices_289, vertices_193, vertices_385, vertices_769, vertices_14, vertices_134, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_216, vertices_536, vertices_552, vertices_648, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_523), (false, vertices_771), (false, vertices_117), (false, vertices_197), (false, vertices_809), (false, vertices_481), (true, vertices_642), (true, vertices_140), (true, vertices_216), (true, vertices_536), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_197) then 2 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_481) then 21 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_216) then 18 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 2 3 5 6 216
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 2 0 5 6 7 386 962 1
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 28 220 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 728
cert_cover_5 4 1 2 3 5 8 216 728 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1022

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1023.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 267, 117, 197, 809, 481, 654, 778, 962, 220, 568, 728, 880, 7, 11, 259, 53, 69, 133, 41, 265, 97, 289, 193, 385, 14, 134, 266, 522, 386, 642, 770, 28, 140, 84, 196, 56, 216, 536, 552, 648, 776, 112, 560, 592, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_267, vertices_117, vertices_197, vertices_809, vertices_481, vertices_654, vertices_778, vertices_962, vertices_220, vertices_568, vertices_728, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_69, vertices_133, vertices_41, vertices_265, vertices_97, vertices_289, vertices_193, vertices_385, vertices_14, vertices_134, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_216, vertices_536, vertices_552, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_267), (false, vertices_117), (false, vertices_197), (false, vertices_809), (false, vertices_481), (true, vertices_522), (true, vertices_642), (true, vertices_770), (true, vertices_140), (true, vertices_216), (true, vertices_536), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_216) then 19 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
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
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_2 1 2 3 5 6 216
cert_row_4 2 0 5 6 7 8 962 386 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 386 962 1
cert_coverFacet 3 220
cert_cover_5 3 1 1 2 3 5 28 220 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 728
cert_cover_5 5 1 2 3 5 8 216 728 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1023

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 781, 961, 214, 122, 202, 300, 308, 724, 788, 488, 880, 7, 11, 131, 13, 517, 265, 385, 641, 769, 22, 134, 58, 74, 138, 82, 194, 44, 268, 52, 212, 276, 532, 292, 644, 772, 104, 296, 200, 392, 112, 304, 592, 784, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_781, vertices_961, vertices_214, vertices_122, vertices_202, vertices_300, vertices_308, vertices_724, vertices_788, vertices_488, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_517, vertices_265, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_58, vertices_74, vertices_138, vertices_82, vertices_194, vertices_44, vertices_268, vertices_52, vertices_212, vertices_276, vertices_532, vertices_292, vertices_644, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_304, vertices_592, vertices_784, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_781), (false, vertices_961), (true, vertices_74), (true, vertices_82), (true, vertices_194), (true, vertices_212), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_112), (true, vertices_304), (true, vertices_592), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
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
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
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
cert_row_2 1 1 3 5 6 212
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 724
cert_cover_5 5 1 1 3 5 8 212 724 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 488
cert_cover_5 7 2 2 4 5 6 104 488 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 112 880 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1024

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1026.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1026

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 395, 533, 121, 201, 721, 526, 778, 962, 812, 372, 852, 488, 7, 11, 131, 21, 517, 57, 73, 137, 81, 529, 193, 641, 14, 518, 266, 522, 386, 642, 770, 44, 524, 52, 340, 532, 292, 772, 104, 296, 200, 392, 776, 112, 592, 352, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_395, vertices_533, vertices_121, vertices_201, vertices_721, vertices_526, vertices_778, vertices_962, vertices_812, vertices_372, vertices_852, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_517, vertices_57, vertices_73, vertices_137, vertices_81, vertices_529, vertices_193, vertices_641, vertices_14, vertices_518, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_340, vertices_532, vertices_292, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_776, vertices_112, vertices_592, vertices_352, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_395), (false, vertices_533), (false, vertices_121), (false, vertices_201), (false, vertices_721), (true, vertices_522), (true, vertices_770), (true, vertices_524), (true, vertices_340), (true, vertices_292), (true, vertices_772), (true, vertices_296), (true, vertices_776), (true, vertices_352), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_340) then 16 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 7 340
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 386 962 1
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 372
cert_cover_5 4 0 1 3 4 5 52 372 3
cert_coverFacet 5 852
cert_cover_5 5 0 1 3 5 8 340 852 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 104 488 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1026

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1027.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1027

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 117, 197, 361, 449, 654, 962, 668, 212, 824, 752, 864, 7, 11, 259, 53, 69, 133, 41, 265, 97, 193, 321, 385, 14, 134, 522, 386, 642, 770, 28, 652, 84, 148, 196, 56, 536, 296, 776, 112, 560, 208, 656, 352, 608, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_117, vertices_197, vertices_361, vertices_449, vertices_654, vertices_962, vertices_668, vertices_212, vertices_824, vertices_752, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_53, vertices_69, vertices_133, vertices_41, vertices_265, vertices_97, vertices_193, vertices_321, vertices_385, vertices_14, vertices_134, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_652, vertices_84, vertices_148, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_117), (false, vertices_197), (false, vertices_361), (false, vertices_449), (true, vertices_642), (true, vertices_652), (true, vertices_148), (true, vertices_536), (true, vertices_560), (true, vertices_208), (true, vertices_656), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_197) then 0 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_652) then 18 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 386 1
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 386 962 1
cert_coverFacet 2 668
cert_cover_5 2 0 1 2 3 6 28 668 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1027

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1028.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 395, 707, 597, 121, 201, 782, 898, 428, 820, 232, 496, 976, 7, 11, 131, 515, 21, 517, 57, 73, 137, 81, 193, 577, 14, 518, 266, 386, 642, 770, 44, 268, 52, 532, 292, 772, 104, 168, 200, 392, 112, 304, 464, 592, 784, 224, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_395, vertices_707, vertices_597, vertices_121, vertices_201, vertices_782, vertices_898, vertices_428, vertices_820, vertices_232, vertices_496, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_21, vertices_517, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_577, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_168, vertices_200, vertices_392, vertices_112, vertices_304, vertices_464, vertices_592, vertices_784, vertices_224, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_395), (false, vertices_707), (false, vertices_597), (false, vertices_121), (false, vertices_201), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_304), (true, vertices_464), (true, vertices_784), (true, vertices_224), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_464) then 21 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 496
cert_cover_5 5 0 3 4 5 6 112 496 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 8 464 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1028

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 395, 707, 597, 121, 201, 782, 898, 300, 436, 916, 488, 752, 7, 11, 131, 515, 21, 517, 57, 73, 137, 81, 193, 577, 14, 518, 266, 386, 642, 770, 44, 268, 52, 404, 532, 292, 772, 104, 296, 200, 392, 112, 176, 592, 656, 224, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_395, vertices_707, vertices_597, vertices_121, vertices_201, vertices_782, vertices_898, vertices_300, vertices_436, vertices_916, vertices_488, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_21, vertices_517, vertices_57, vertices_73, vertices_137, vertices_81, vertices_193, vertices_577, vertices_14, vertices_518, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_404, vertices_532, vertices_292, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_395), (false, vertices_707), (false, vertices_597), (false, vertices_121), (false, vertices_201), (true, vertices_770), (true, vertices_268), (true, vertices_404), (true, vertices_292), (true, vertices_772), (true, vertices_296), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 15 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_404) then 20 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
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
cert_row_4 0 0 1 2 7 8 782 14 3
cert_row_2 1 1 3 6 7 404
cert_row_4 2 2 4 5 6 7 488 104 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 8 404 916 3
cert_coverFacet 5 488
cert_cover_5 5 2 2 4 5 6 104 488 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1029

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1030.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1030

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 779, 597, 425, 817, 398, 710, 962, 124, 204, 232, 496, 848, 7, 11, 515, 21, 517, 41, 265, 49, 529, 289, 769, 14, 134, 518, 266, 706, 386, 770, 60, 76, 140, 84, 196, 580, 104, 168, 200, 392, 112, 304, 336, 592, 784, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_597, vertices_425, vertices_817, vertices_398, vertices_710, vertices_962, vertices_124, vertices_204, vertices_232, vertices_496, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_266, vertices_706, vertices_386, vertices_770, vertices_60, vertices_76, vertices_140, vertices_84, vertices_196, vertices_580, vertices_104, vertices_168, vertices_200, vertices_392, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_134), (true, vertices_706), (true, vertices_386), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_336), (true, vertices_224), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_706) then 15 else
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
cert_nodeAtPriority_17 519 134 386 76 140 196 104 200 112 336 224 448 832 779 706 63 597 425 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 8 706
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 710
cert_cover_5 1 0 0 1 5 6 134 710 2
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 706 962 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1030

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 142, 394, 796, 396, 468, 632, 976, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 138, 266, 386, 28, 140, 268, 84, 276, 196, 388, 56, 536, 552, 392, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_142, vertices_394, vertices_796, vertices_396, vertices_468, vertices_632, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_138, vertices_266, vertices_386, vertices_28, vertices_140, vertices_268, vertices_84, vertices_276, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_392, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_138), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_388), (true, vertices_536), (true, vertices_392), (true, vertices_464), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_737) then 21 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_464) then 19 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_rows_3
cert_pivot_3 1 6 2
cert_heightProof 3
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 396
cert_cover_2 3 2 1 6 7 140 396 3
cert_coverFacet 4 468
cert_cover_5 4 0 1 3 5 6 84 468 3
cert_coverFacet 5 632
cert_cover_5 5 2 2 3 4 5 56 632 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 8 464 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1034

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 203, 405, 121, 849, 961, 270, 390, 906, 812, 628, 788, 744, 7, 11, 131, 21, 133, 57, 73, 81, 273, 193, 833, 385, 14, 134, 262, 138, 266, 386, 44, 268, 52, 276, 532, 548, 388, 772, 104, 552, 200, 648, 776, 112, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_203, vertices_405, vertices_121, vertices_849, vertices_961, vertices_270, vertices_390, vertices_906, vertices_812, vertices_628, vertices_788, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_833, vertices_385, vertices_14, vertices_134, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_532, vertices_548, vertices_388, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_203), (false, vertices_405), (false, vertices_121), (false, vertices_849), (false, vertices_961), (true, vertices_262), (true, vertices_266), (true, vertices_386), (true, vertices_268), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 16 19 20 21 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 906
cert_cover_5 2 0 0 2 6 7 138 906 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 628
cert_cover_5 4 2 1 3 4 5 52 628 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1035

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 135, 203, 405, 121, 337, 961, 270, 390, 906, 812, 628, 852, 744, 7, 11, 131, 21, 133, 57, 73, 81, 273, 193, 321, 385, 14, 134, 262, 138, 266, 386, 44, 268, 52, 596, 276, 548, 388, 772, 104, 552, 200, 648, 776, 112, 336, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_135, vertices_203, vertices_405, vertices_121, vertices_337, vertices_961, vertices_270, vertices_390, vertices_906, vertices_812, vertices_628, vertices_852, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_321, vertices_385, vertices_14, vertices_134, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_596, vertices_276, vertices_548, vertices_388, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_336, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_135), (false, vertices_203), (false, vertices_405), (false, vertices_121), (false, vertices_337), (false, vertices_961), (true, vertices_262), (true, vertices_266), (true, vertices_386), (true, vertices_268), (true, vertices_596), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 17 14 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_135) then 0 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_596) then 19 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_135), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
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
cert_row_2 0 1 3 5 8 596
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 906
cert_cover_5 2 1 0 2 6 7 138 906 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 628
cert_cover_5 4 0 1 3 4 5 52 628 3
cert_coverFacet 5 852
cert_cover_5 5 0 1 3 5 7 596 852 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 104 744 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1036

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 387, 341, 121, 961, 782, 906, 684, 820, 232, 752, 848, 7, 11, 131, 259, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 778, 386, 44, 524, 52, 276, 548, 772, 104, 168, 200, 648, 112, 560, 336, 592, 784, 224, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_387, vertices_341, vertices_121, vertices_961, vertices_782, vertices_906, vertices_684, vertices_820, vertices_232, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_387), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 20 14 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_778) then 19 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1038

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 387, 789, 121, 465, 782, 906, 684, 628, 232, 848, 992, 7, 11, 131, 259, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 778, 386, 44, 524, 52, 532, 548, 772, 104, 168, 200, 648, 112, 336, 592, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_387, vertices_789, vertices_121, vertices_465, vertices_782, vertices_906, vertices_684, vertices_628, vertices_232, vertices_848, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_387), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_778), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_648), (true, vertices_592), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 12 21 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_778) then 20 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
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
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1039

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 203, 387, 771, 789, 121, 465, 654, 898, 812, 372, 744, 992, 7, 11, 131, 259, 515, 21, 517, 57, 73, 81, 273, 193, 385, 769, 14, 518, 138, 386, 642, 770, 44, 524, 52, 276, 292, 772, 104, 552, 200, 648, 112, 336, 736, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_203, vertices_387, vertices_771, vertices_789, vertices_121, vertices_465, vertices_654, vertices_898, vertices_812, vertices_372, vertices_744, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_515, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_769, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_336, vertices_736, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_203), (false, vertices_387), (false, vertices_771), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_642), (true, vertices_524), (true, vertices_292), (true, vertices_552), (true, vertices_648), (true, vertices_736), (true, vertices_352), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 15 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_771) then 2 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_736) then 21 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 4 5 6 8 736
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 372
cert_cover_5 3 3 1 3 4 5 52 372 3
cert_coverFacet 4 744
cert_cover_5 4 1 2 4 5 6 104 744 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 7 736 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1040

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 533, 121, 209, 913, 398, 812, 628, 488, 720, 992, 7, 11, 131, 259, 21, 517, 57, 73, 81, 145, 529, 193, 385, 769, 14, 262, 138, 386, 44, 268, 52, 532, 548, 772, 104, 296, 200, 392, 112, 208, 592, 656, 480, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_533, vertices_121, vertices_209, vertices_913, vertices_398, vertices_812, vertices_628, vertices_488, vertices_720, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_145, vertices_529, vertices_193, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_208, vertices_592, vertices_656, vertices_480, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_533), (false, vertices_121), (false, vertices_209), (false, vertices_913), (true, vertices_268), (true, vertices_548), (true, vertices_296), (true, vertices_392), (true, vertices_592), (true, vertices_480), (true, vertices_608), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 15 18 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_209) then 2 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_480) then 21 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 4 5 6 7 480
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 812
cert_cover_5 1 2 1 2 4 7 44 812 3
cert_coverFacet 2 628
cert_cover_5 2 3 1 3 4 5 52 628 3
cert_coverFacet 3 488
cert_cover_5 3 1 2 4 5 6 104 488 3
cert_coverFacet 4 720
cert_cover_2 4 5 3 6 8 208 720 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 8 480 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1041

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 533, 121, 209, 913, 398, 364, 564, 868, 968, 752, 7, 11, 131, 259, 21, 517, 57, 73, 81, 145, 529, 193, 385, 769, 14, 262, 138, 386, 44, 268, 52, 532, 356, 548, 772, 104, 200, 328, 392, 112, 560, 208, 656, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_533, vertices_121, vertices_209, vertices_913, vertices_398, vertices_364, vertices_564, vertices_868, vertices_968, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_145, vertices_529, vertices_193, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_356, vertices_548, vertices_772, vertices_104, vertices_200, vertices_328, vertices_392, vertices_112, vertices_560, vertices_208, vertices_656, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_533), (false, vertices_121), (false, vertices_209), (false, vertices_913), (true, vertices_268), (true, vertices_356), (true, vertices_548), (true, vertices_328), (true, vertices_392), (true, vertices_560), (true, vertices_608), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_209) then 2 else
  if p.val = (false, vertices_913) then 20 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_356) then 15 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 1 4 5 7 356
cert_row_4 2 2 5 6 7 8 968 200 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 364
cert_cover_5 1 1 1 2 4 5 44 364 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 868
cert_cover_5 3 1 1 4 5 8 356 868 3
cert_coverFacet 4 968
cert_cover_5 4 2 2 5 6 7 200 968 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1042

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1043.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1043

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 533, 809, 625, 206, 390, 124, 212, 916, 488, 976, 864, 7, 11, 259, 21, 517, 41, 265, 49, 529, 545, 769, 14, 134, 262, 138, 386, 60, 76, 84, 148, 532, 196, 388, 772, 104, 296, 200, 392, 112, 208, 592, 912, 352, 608, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_533, vertices_809, vertices_625, vertices_206, vertices_390, vertices_124, vertices_212, vertices_916, vertices_488, vertices_976, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_769, vertices_14, vertices_134, vertices_262, vertices_138, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_532, vertices_196, vertices_388, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_112, vertices_208, vertices_592, vertices_912, vertices_352, vertices_608, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_533), (false, vertices_809), (false, vertices_625), (true, vertices_134), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_104), (true, vertices_200), (true, vertices_208), (true, vertices_912), (true, vertices_352), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_912) then 22 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_912), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 6 7 8 912
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 2 5 6 206 14 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 916
cert_cover_5 4 0 1 3 6 7 148 916 3
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 7 208 976 3
cert_coverFacet 7 864
cert_cover_2 7 5 4 7 8 352 864 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1043

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1044.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1044

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 533, 809, 625, 206, 390, 124, 468, 788, 744, 904, 976, 7, 11, 259, 21, 517, 41, 265, 49, 529, 545, 769, 14, 134, 262, 138, 386, 60, 76, 84, 276, 532, 196, 388, 772, 104, 552, 200, 392, 648, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_533, vertices_809, vertices_625, vertices_206, vertices_390, vertices_124, vertices_468, vertices_788, vertices_744, vertices_904, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_545, vertices_769, vertices_14, vertices_134, vertices_262, vertices_138, vertices_386, vertices_60, vertices_76, vertices_84, vertices_276, vertices_532, vertices_196, vertices_388, vertices_772, vertices_104, vertices_552, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_533), (false, vertices_809), (false, vertices_625), (true, vertices_134), (true, vertices_76), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_104), (true, vertices_200), (true, vertices_648), (true, vertices_464), (true, vertices_784), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_809) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_464) then 22 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
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
cert_row_2 0 3 5 6 7 464
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 2 5 6 206 14 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 468
cert_cover_5 3 0 1 3 5 6 84 468 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coverFacet 7 976
cert_cover_5 7 0 3 5 6 8 464 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1044

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1047.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1047

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 533, 121, 465, 785, 398, 684, 564, 964, 744, 880, 7, 11, 131, 259, 21, 517, 57, 73, 81, 273, 529, 193, 385, 769, 14, 262, 138, 386, 44, 140, 52, 532, 548, 388, 644, 772, 104, 680, 200, 112, 560, 336, 784, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_533, vertices_121, vertices_465, vertices_785, vertices_398, vertices_684, vertices_564, vertices_964, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_273, vertices_529, vertices_193, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_140, vertices_52, vertices_532, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_680, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_533), (false, vertices_121), (false, vertices_465), (false, vertices_785), (true, vertices_140), (true, vertices_548), (true, vertices_388), (true, vertices_644), (true, vertices_680), (true, vertices_560), (true, vertices_608), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 19 15 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_465) then 18 else
  if p.val = (false, vertices_785) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_680) then 20 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 2 4 6 8 680
cert_row_4 2 1 5 6 7 8 964 388 1
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 684
cert_cover_5 1 1 1 2 4 6 44 684 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 964
cert_cover_5 3 2 1 5 6 7 388 964 1
cert_coverFacet 4 744
cert_cover_5 4 1 2 4 5 6 104 744 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1047

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1048.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1048

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 395, 533, 169, 625, 929, 206, 390, 124, 468, 788, 744, 976, 7, 11, 259, 21, 517, 41, 137, 49, 529, 161, 545, 385, 769, 14, 134, 262, 138, 386, 60, 76, 84, 276, 532, 196, 388, 772, 104, 168, 200, 112, 464, 592, 784, 608, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_533, vertices_169, vertices_625, vertices_929, vertices_206, vertices_390, vertices_124, vertices_468, vertices_788, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_545, vertices_385, vertices_769, vertices_14, vertices_134, vertices_262, vertices_138, vertices_386, vertices_60, vertices_76, vertices_84, vertices_276, vertices_532, vertices_196, vertices_388, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_533), (false, vertices_169), (false, vertices_625), (false, vertices_929), (true, vertices_134), (true, vertices_76), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_104), (true, vertices_200), (true, vertices_464), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 18 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_464) then 20 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 2 5 6 206 14 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 468
cert_cover_5 3 0 1 3 5 6 84 468 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 8 464 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1048

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1049.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1049

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 597, 121, 961, 398, 172, 436, 788, 744, 624, 944, 7, 11, 131, 259, 21, 517, 57, 73, 81, 193, 577, 385, 769, 14, 262, 138, 386, 44, 140, 52, 276, 532, 164, 388, 772, 104, 168, 200, 112, 432, 560, 592, 784, 608, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_597, vertices_121, vertices_961, vertices_398, vertices_172, vertices_436, vertices_788, vertices_744, vertices_624, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_140, vertices_52, vertices_276, vertices_532, vertices_164, vertices_388, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_432, vertices_560, vertices_592, vertices_784, vertices_608, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_597), (false, vertices_121), (false, vertices_961), (true, vertices_140), (true, vertices_276), (true, vertices_164), (true, vertices_388), (true, vertices_168), (true, vertices_432), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_432) then 19 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_rows_3
cert_pivot_3 0 3 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 172
cert_cover_2 1 2 1 4 6 44 172 3
cert_coverFacet 2 436
cert_cover_5 2 0 1 3 4 6 52 436 3
cert_coverFacet 3 788
cert_cover_2 3 3 1 7 8 276 788 3
cert_coverFacet 4 744
cert_cover_5 4 2 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1049

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1051.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1051

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 597, 121, 961, 398, 428, 308, 788, 744, 624, 944, 7, 11, 131, 259, 21, 517, 57, 73, 81, 193, 577, 385, 769, 14, 262, 138, 386, 44, 396, 52, 276, 532, 292, 772, 104, 168, 200, 112, 304, 560, 592, 784, 608, 416, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_597, vertices_121, vertices_961, vertices_398, vertices_428, vertices_308, vertices_788, vertices_744, vertices_624, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_396, vertices_52, vertices_276, vertices_532, vertices_292, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_304, vertices_560, vertices_592, vertices_784, vertices_608, vertices_416, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_597), (false, vertices_121), (false, vertices_961), (true, vertices_396), (true, vertices_276), (true, vertices_292), (true, vertices_168), (true, vertices_304), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_396) then 15 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 2 4 5 6 8 744 104 3
cert_row_4 2 3 4 6 7 8 944 304 2
cert_rows_3
cert_pivot_3 2 1 3
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 428
cert_cover_5 1 0 1 2 4 6 44 428 3
cert_coverFacet 2 308
cert_cover_2 2 3 1 4 7 52 308 3
cert_coverFacet 3 788
cert_cover_2 3 3 1 7 8 276 788 3
cert_coverFacet 4 744
cert_cover_5 4 1 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 944
cert_cover_5 6 2 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1051

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1052.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1052

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 405, 121, 209, 526, 906, 620, 820, 712, 496, 992, 7, 11, 131, 259, 21, 261, 57, 73, 81, 145, 193, 385, 14, 518, 138, 522, 386, 770, 44, 524, 52, 276, 548, 772, 104, 200, 584, 648, 112, 304, 208, 400, 480, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_405, vertices_121, vertices_209, vertices_526, vertices_906, vertices_620, vertices_820, vertices_712, vertices_496, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_385, vertices_14, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_304, vertices_208, vertices_400, vertices_480, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_405), (false, vertices_121), (false, vertices_209), (true, vertices_522), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_304), (true, vertices_480), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_480) then 22 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_2 1 4 5 6 7 480
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 2 1 2 4 5 44 620 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 712
cert_cover_2 4 5 2 6 8 200 712 3
cert_coverFacet 5 496
cert_cover_5 5 1 3 4 5 6 112 496 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 8 480 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1052

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1053.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1053

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 405, 121, 209, 526, 906, 556, 372, 868, 744, 976, 7, 11, 131, 259, 21, 261, 57, 73, 81, 145, 193, 385, 14, 518, 138, 522, 386, 770, 44, 524, 52, 276, 356, 548, 772, 104, 552, 200, 648, 112, 208, 336, 400, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_405, vertices_121, vertices_209, vertices_526, vertices_906, vertices_556, vertices_372, vertices_868, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_145, vertices_193, vertices_385, vertices_14, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_356, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_208, vertices_336, vertices_400, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_405), (false, vertices_121), (false, vertices_209), (true, vertices_522), (true, vertices_524), (true, vertices_356), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_336), (true, vertices_608), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_356) then 17 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
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
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 372
cert_cover_5 3 0 1 3 4 5 52 372 3
cert_coverFacet 4 868
cert_cover_5 4 0 1 4 5 8 356 868 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1053

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1054.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1054

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 341, 121, 449, 526, 906, 684, 820, 232, 752, 976, 7, 11, 131, 259, 21, 261, 57, 73, 81, 193, 321, 385, 14, 518, 138, 522, 386, 770, 44, 524, 52, 276, 548, 772, 104, 168, 200, 648, 112, 560, 720, 336, 784, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_341, vertices_121, vertices_449, vertices_526, vertices_906, vertices_684, vertices_820, vertices_232, vertices_752, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_560, vertices_720, vertices_336, vertices_784, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_341), (false, vertices_121), (false, vertices_449), (true, vertices_522), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_720), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_449) then 1 else
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
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
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
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1054

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1055.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1055

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 341, 121, 449, 526, 906, 556, 692, 916, 744, 496, 7, 11, 131, 259, 21, 261, 57, 73, 81, 193, 321, 385, 14, 518, 138, 522, 386, 770, 44, 524, 52, 660, 276, 548, 772, 104, 552, 200, 648, 112, 176, 336, 400, 224, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_341, vertices_121, vertices_449, vertices_526, vertices_906, vertices_556, vertices_692, vertices_916, vertices_744, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_660, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_341), (false, vertices_121), (false, vertices_449), (true, vertices_522), (true, vertices_524), (true, vertices_660), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 15 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_449) then 1 else
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
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
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
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1055

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1056.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1056

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 277, 121, 465, 526, 906, 684, 628, 852, 232, 992, 7, 11, 131, 259, 21, 261, 57, 73, 81, 273, 193, 385, 14, 518, 138, 522, 386, 770, 44, 524, 52, 596, 276, 548, 772, 104, 168, 200, 648, 112, 336, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_277, vertices_121, vertices_465, vertices_526, vertices_906, vertices_684, vertices_628, vertices_852, vertices_232, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_596, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_336, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_277), (false, vertices_121), (false, vertices_465), (true, vertices_522), (true, vertices_524), (true, vertices_596), (true, vertices_548), (true, vertices_168), (true, vertices_648), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_596) then 16 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
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
cert_row_2 0 1 3 5 8 596
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 3 0 1 4
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 52 628 3
cert_coverFacet 4 852
cert_cover_5 4 0 1 3 5 7 596 852 3
cert_coverFacet 5 232
cert_cover_2 5 4 2 5 6 104 232 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1056

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 277, 121, 465, 526, 906, 620, 436, 932, 712, 752, 7, 11, 131, 259, 21, 261, 57, 73, 81, 273, 193, 385, 14, 518, 138, 522, 386, 770, 44, 524, 52, 276, 420, 548, 772, 104, 200, 584, 648, 112, 176, 208, 400, 608, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_277, vertices_121, vertices_465, vertices_526, vertices_906, vertices_620, vertices_436, vertices_932, vertices_712, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_518, vertices_138, vertices_522, vertices_386, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_420, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_176, vertices_208, vertices_400, vertices_608, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_277), (false, vertices_121), (false, vertices_465), (true, vertices_522), (true, vertices_524), (true, vertices_420), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_176), (true, vertices_608), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_420) then 16 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
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
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_2 1 1 4 6 7 420
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 7 1 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 620
cert_cover_5 2 2 1 2 4 5 44 620 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 932
cert_cover_5 4 1 1 4 6 8 420 932 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 752
cert_cover_5 6 3 3 4 5 6 112 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1057

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1320 : Certifies 1320 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1020.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1321 : Certifies 1321 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1021.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1322 : Certifies 1322 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1022.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1323 : Certifies 1323 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1023.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1324 : Certifies 1324 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1325 : Certifies 1325 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1026.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1326 : Certifies 1326 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1027.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1327 : Certifies 1327 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1028.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1328 : Certifies 1328 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1329 : Certifies 1329 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1030.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1330 : Certifies 1330 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1331 : Certifies 1331 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1332 : Certifies 1332 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1333 : Certifies 1333 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1334 : Certifies 1334 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1335 : Certifies 1335 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1336 : Certifies 1336 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1337 : Certifies 1337 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1338 : Certifies 1338 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1043.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1339 : Certifies 1339 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1044.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1340 : Certifies 1340 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1047.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1341 : Certifies 1341 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1048.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1342 : Certifies 1342 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1049.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1343 : Certifies 1343 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1051.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1344 : Certifies 1344 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1052.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1345 : Certifies 1345 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1053.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1346 : Certifies 1346 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1054.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1347 : Certifies 1347 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1055.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1348 : Certifies 1348 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1056.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1349 : Certifies 1349 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B044 (j : Fin 30) :
    Certifies (1320 + j.val) := by
  fin_cases j
  · exact projection_1320
  · exact projection_1321
  · exact projection_1322
  · exact projection_1323
  · exact projection_1324
  · exact projection_1325
  · exact projection_1326
  · exact projection_1327
  · exact projection_1328
  · exact projection_1329
  · exact projection_1330
  · exact projection_1331
  · exact projection_1332
  · exact projection_1333
  · exact projection_1334
  · exact projection_1335
  · exact projection_1336
  · exact projection_1337
  · exact projection_1338
  · exact projection_1339
  · exact projection_1340
  · exact projection_1341
  · exact projection_1342
  · exact projection_1343
  · exact projection_1344
  · exact projection_1345
  · exact projection_1346
  · exact projection_1347
  · exact projection_1348
  · exact projection_1349

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
