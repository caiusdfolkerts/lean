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
/- Source: ProjectionCertificates/R_one_six_0394.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0394

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 525, 837, 214, 282, 402, 620, 244, 696, 920, 992, 7, 11, 67, 259, 13, 69, 517, 521, 321, 769, 22, 70, 26, 266, 146, 274, 194, 386, 44, 524, 52, 212, 100, 580, 56, 664, 280, 552, 776, 176, 400, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_525, vertices_837, vertices_214, vertices_282, vertices_402, vertices_620, vertices_244, vertices_696, vertices_920, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_517, vertices_521, vertices_321, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_274, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_212, vertices_100, vertices_580, vertices_56, vertices_664, vertices_280, vertices_552, vertices_776, vertices_176, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_525), (false, vertices_837), (true, vertices_146), (true, vertices_274), (true, vertices_212), (true, vertices_100), (true, vertices_664), (true, vertices_280), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_212) then 19 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_664) then 21 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 4 5 6 7 8 992 224 3
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_2 2 2 3 6 8 664
cert_row_2 3 1 3 5 6 212
cert_rows
cert_pivot_2 7 4 2 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 3 0 1 3 5 22 214 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 620
cert_cover_5 3 1 1 2 4 5 44 620 3
cert_coverFacet 4 244
cert_cover_5 4 3 1 3 4 5 52 244 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 920
cert_cover_5 6 2 2 3 6 7 664 920 3
cert_coverFacet 7 992
cert_cover_5 7 0 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0394

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0395.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0395

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 525, 837, 214, 410, 620, 244, 824, 944, 736, 960, 7, 11, 67, 259, 13, 69, 517, 521, 321, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 212, 100, 580, 56, 280, 552, 776, 176, 816, 400, 224, 608, 672, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_525, vertices_837, vertices_214, vertices_410, vertices_620, vertices_244, vertices_824, vertices_944, vertices_736, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_517, vertices_521, vertices_321, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_212, vertices_100, vertices_580, vertices_56, vertices_280, vertices_552, vertices_776, vertices_176, vertices_816, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_525), (false, vertices_837), (true, vertices_146), (true, vertices_212), (true, vertices_100), (true, vertices_280), (true, vertices_552), (true, vertices_176), (true, vertices_816), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_212) then 19 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_816) then 22 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_2 1 3 4 7 8 816
cert_row_2 2 1 3 5 6 212
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 0 7 3 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 26 410 3
cert_coverFacet 2 620
cert_cover_5 2 3 1 2 4 5 44 620 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 52 244 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 944
cert_cover_5 5 1 3 4 6 7 176 944 3
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0395

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0396.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0396

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 525, 837, 214, 410, 620, 244, 568, 792, 944, 992, 7, 11, 67, 259, 13, 69, 517, 521, 321, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 212, 100, 580, 56, 280, 536, 552, 776, 176, 560, 400, 784, 224, 608, 928, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_525, vertices_837, vertices_214, vertices_410, vertices_620, vertices_244, vertices_568, vertices_792, vertices_944, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_517, vertices_521, vertices_321, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_212, vertices_100, vertices_580, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_176, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608, vertices_928, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_525), (false, vertices_837), (true, vertices_146), (true, vertices_212), (true, vertices_100), (true, vertices_280), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_400), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_928)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_212) then 19 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_928) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(true, vertices_928), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_2 1 4 6 7 8 928
cert_row_2 2 1 3 5 6 212
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 0 7 3 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 26 410 3
cert_coverFacet 2 620
cert_cover_5 2 3 1 2 4 5 44 620 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 52 244 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 176 944 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0396

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0397.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0397

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 405, 197, 793, 590, 834, 236, 180, 632, 944, 992, 7, 11, 67, 259, 21, 69, 133, 25, 777, 273, 193, 385, 14, 70, 522, 322, 578, 770, 44, 76, 52, 148, 164, 196, 56, 536, 104, 584, 176, 560, 400, 784, 224, 608, 928, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_405, vertices_197, vertices_793, vertices_590, vertices_834, vertices_236, vertices_180, vertices_632, vertices_944, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_133, vertices_25, vertices_777, vertices_273, vertices_193, vertices_385, vertices_14, vertices_70, vertices_522, vertices_322, vertices_578, vertices_770, vertices_44, vertices_76, vertices_52, vertices_148, vertices_164, vertices_196, vertices_56, vertices_536, vertices_104, vertices_584, vertices_176, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608, vertices_928, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_405), (false, vertices_197), (false, vertices_793), (true, vertices_578), (true, vertices_76), (true, vertices_164), (true, vertices_104), (true, vertices_584), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_928), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_928) then 22 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(true, vertices_928), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 6 7 8 928
cert_row_4 1 0 1 2 5 8 590 14 3
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 14 590 3
cert_coverFacet 1 834
cert_cover_2 1 5 0 7 8 322 834 3
cert_coverFacet 2 236
cert_cover_5 2 2 1 2 4 5 44 236 3
cert_coverFacet 3 180
cert_cover_2 3 3 1 4 6 52 180 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 944
cert_cover_5 5 0 3 4 6 7 176 944 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0397

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0398.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0398

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 405, 197, 617, 241, 782, 454, 834, 796, 696, 912, 992, 7, 11, 67, 21, 69, 133, 41, 585, 49, 145, 97, 193, 14, 70, 262, 522, 322, 578, 770, 28, 780, 276, 196, 388, 56, 536, 552, 176, 400, 656, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_405, vertices_197, vertices_617, vertices_241, vertices_782, vertices_454, vertices_834, vertices_796, vertices_696, vertices_912, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_322, vertices_578, vertices_770, vertices_28, vertices_780, vertices_276, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_176, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_405), (false, vertices_197), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_656), (true, vertices_784), (true, vertices_672), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 13 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 18 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 2 7 8 780
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 28 796 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 912
cert_cover_2 5 6 3 7 8 400 912 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0398

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0399.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0399

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 405, 197, 233, 433, 782, 454, 834, 796, 632, 816, 992, 7, 11, 67, 21, 69, 133, 41, 73, 49, 401, 161, 193, 14, 70, 262, 522, 322, 578, 770, 28, 780, 276, 196, 388, 56, 536, 104, 584, 304, 560, 784, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_405, vertices_197, vertices_233, vertices_433, vertices_782, vertices_454, vertices_834, vertices_796, vertices_632, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_133, vertices_41, vertices_73, vertices_49, vertices_401, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_322, vertices_578, vertices_770, vertices_28, vertices_780, vertices_276, vertices_196, vertices_388, vertices_56, vertices_536, vertices_104, vertices_584, vertices_304, vertices_560, vertices_784, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_405), (false, vertices_197), (false, vertices_233), (false, vertices_433), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 2 7 8 780
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 28 796 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0399

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0400.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0400

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 523, 835, 213, 617, 241, 782, 454, 796, 404, 696, 912, 992, 7, 11, 67, 515, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 522, 322, 770, 28, 780, 148, 276, 196, 388, 56, 536, 552, 176, 400, 656, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_523, vertices_835, vertices_213, vertices_617, vertices_241, vertices_782, vertices_454, vertices_796, vertices_404, vertices_696, vertices_912, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_522, vertices_322, vertices_770, vertices_28, vertices_780, vertices_148, vertices_276, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_176, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_523), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_780), (true, vertices_276), (true, vertices_388), (true, vertices_536), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_523) then 1 else
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 2 7 8 780
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 404
cert_cover_2 3 3 1 6 7 148 404 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 912
cert_cover_2 5 6 3 7 8 400 912 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0400

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0401.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0401

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 85, 217, 905, 526, 838, 556, 372, 932, 696, 496, 7, 11, 67, 259, 21, 69, 25, 137, 777, 81, 193, 385, 14, 70, 518, 522, 322, 770, 44, 524, 52, 84, 292, 548, 324, 772, 56, 152, 552, 648, 368, 176, 208, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_85, vertices_217, vertices_905, vertices_526, vertices_838, vertices_556, vertices_372, vertices_932, vertices_696, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_137, vertices_777, vertices_81, vertices_193, vertices_385, vertices_14, vertices_70, vertices_518, vertices_522, vertices_322, vertices_770, vertices_44, vertices_524, vertices_52, vertices_84, vertices_292, vertices_548, vertices_324, vertices_772, vertices_56, vertices_152, vertices_552, vertices_648, vertices_368, vertices_176, vertices_208, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_85), (false, vertices_217), (false, vertices_905), (true, vertices_518), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_772), (true, vertices_552), (true, vertices_368), (true, vertices_176), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 16 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_217) then 18 else
  if p.val = (false, vertices_905) then 19 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_368) then 21 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 70 3
cert_row_2 1 3 4 5 7 368
cert_row_4 2 1 4 6 7 8 932 292 2
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 52 372 3
cert_coverFacet 4 932
cert_cover_5 4 2 1 4 6 7 292 932 2
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 496
cert_cover_5 6 1 3 4 5 6 368 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0401

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0402.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0402

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 779, 533, 617, 689, 78, 454, 330, 220, 916, 248, 840, 992, 7, 11, 771, 21, 517, 41, 521, 49, 529, 545, 14, 70, 262, 74, 266, 322, 28, 76, 148, 532, 196, 388, 772, 56, 216, 104, 328, 584, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_779, vertices_533, vertices_617, vertices_689, vertices_78, vertices_454, vertices_330, vertices_220, vertices_916, vertices_248, vertices_840, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_771, vertices_21, vertices_517, vertices_41, vertices_521, vertices_49, vertices_529, vertices_545, vertices_14, vertices_70, vertices_262, vertices_74, vertices_266, vertices_322, vertices_28, vertices_76, vertices_148, vertices_532, vertices_196, vertices_388, vertices_772, vertices_56, vertices_216, vertices_104, vertices_328, vertices_584, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_779), (false, vertices_533), (false, vertices_617), (false, vertices_689), (true, vertices_70), (true, vertices_74), (true, vertices_322), (true, vertices_76), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_328), (true, vertices_224), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_216) then 20 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
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
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 220
cert_cover_5 3 0 1 2 3 5 28 220 3
cert_coverFacet 4 916
cert_cover_5 4 2 1 3 6 7 148 916 3
cert_coverFacet 5 248
cert_cover_5 5 0 2 3 4 5 56 248 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0402

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0403.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0403

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 195, 899, 85, 681, 241, 270, 454, 796, 852, 632, 992, 7, 11, 67, 131, 771, 21, 69, 41, 521, 49, 81, 161, 193, 641, 14, 70, 262, 266, 194, 386, 28, 268, 84, 788, 324, 56, 536, 552, 776, 112, 592, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_195, vertices_899, vertices_85, vertices_681, vertices_241, vertices_270, vertices_454, vertices_796, vertices_852, vertices_632, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_771, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_161, vertices_193, vertices_641, vertices_14, vertices_70, vertices_262, vertices_266, vertices_194, vertices_386, vertices_28, vertices_268, vertices_84, vertices_788, vertices_324, vertices_56, vertices_536, vertices_552, vertices_776, vertices_112, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_195), (false, vertices_899), (false, vertices_85), (false, vertices_681), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_788), (true, vertices_324), (true, vertices_536), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_85) then 2 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_788) then 16 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
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
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 7 84 852 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0403

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0404.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0404

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 451, 341, 793, 206, 906, 236, 820, 868, 696, 736, 960, 7, 11, 67, 259, 21, 69, 25, 265, 273, 321, 14, 70, 138, 266, 194, 386, 44, 204, 52, 276, 100, 804, 324, 56, 536, 168, 648, 776, 560, 784, 224, 608, 672, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_451, vertices_341, vertices_793, vertices_206, vertices_906, vertices_236, vertices_820, vertices_868, vertices_696, vertices_736, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_273, vertices_321, vertices_14, vertices_70, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_204, vertices_52, vertices_276, vertices_100, vertices_804, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_776, vertices_560, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_451), (false, vertices_341), (false, vertices_793), (true, vertices_138), (true, vertices_204), (true, vertices_100), (true, vertices_804), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_793) then 17 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_204) then 18 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_804) then 21 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_2 1 1 4 7 8 804
cert_row_4 2 0 2 6 7 8 906 138 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 5 1 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 906
cert_cover_5 1 2 0 2 6 7 138 906 3
cert_coverFacet 2 236
cert_cover_5 2 0 1 2 4 5 44 236 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 868
cert_cover_5 4 1 1 4 5 7 100 868 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0404

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0405.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0405

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 899, 789, 233, 689, 78, 454, 796, 332, 632, 840, 992, 7, 11, 131, 259, 21, 261, 41, 201, 49, 529, 161, 641, 769, 14, 70, 262, 74, 194, 386, 28, 76, 268, 788, 324, 56, 536, 104, 328, 584, 776, 560, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_899, vertices_789, vertices_233, vertices_689, vertices_78, vertices_454, vertices_796, vertices_332, vertices_632, vertices_840, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_41, vertices_201, vertices_49, vertices_529, vertices_161, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_194, vertices_386, vertices_28, vertices_76, vertices_268, vertices_788, vertices_324, vertices_56, vertices_536, vertices_104, vertices_328, vertices_584, vertices_776, vertices_560, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_899), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_70), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_536), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_608), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
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
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 332
cert_cover_2 3 2 1 5 7 76 332 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0405

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0406.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0406

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 837, 233, 625, 270, 454, 906, 284, 696, 792, 992, 7, 11, 67, 21, 69, 773, 41, 201, 49, 529, 97, 577, 14, 70, 262, 138, 266, 194, 386, 28, 268, 276, 324, 56, 280, 536, 168, 648, 776, 560, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_837, vertices_233, vertices_625, vertices_270, vertices_454, vertices_906, vertices_284, vertices_696, vertices_792, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_773, vertices_41, vertices_201, vertices_49, vertices_529, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_138, vertices_266, vertices_194, vertices_386, vertices_28, vertices_268, vertices_276, vertices_324, vertices_56, vertices_280, vertices_536, vertices_168, vertices_648, vertices_776, vertices_560, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_837), (false, vertices_233), (false, vertices_625), (true, vertices_262), (true, vertices_266), (true, vertices_386), (true, vertices_268), (true, vertices_280), (true, vertices_536), (true, vertices_648), (true, vertices_776), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 13 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 906
cert_cover_5 2 1 0 2 6 7 138 906 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0406

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0407.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0407

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 451, 205, 905, 278, 326, 794, 236, 628, 852, 696, 992, 7, 11, 67, 259, 13, 69, 137, 265, 193, 385, 22, 70, 262, 26, 266, 274, 322, 44, 204, 52, 596, 276, 100, 324, 56, 536, 168, 648, 776, 560, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_451, vertices_205, vertices_905, vertices_278, vertices_326, vertices_794, vertices_236, vertices_628, vertices_852, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_137, vertices_265, vertices_193, vertices_385, vertices_22, vertices_70, vertices_262, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_204, vertices_52, vertices_596, vertices_276, vertices_100, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_776, vertices_560, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_451), (false, vertices_205), (false, vertices_905), (true, vertices_262), (true, vertices_274), (true, vertices_596), (true, vertices_276), (true, vertices_100), (true, vertices_324), (true, vertices_536), (true, vertices_168), (true, vertices_560), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_596) then 20 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
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
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 26 794 3
cert_coverFacet 3 236
cert_cover_5 3 4 1 2 4 5 44 236 3
cert_coverFacet 4 628
cert_cover_5 4 3 1 3 4 5 52 628 3
cert_coverFacet 5 852
cert_cover_5 5 3 1 3 5 7 596 852 3
cert_coverFacet 6 696
cert_cover_5 6 2 2 3 4 6 56 696 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0407

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0408.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0408

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 397, 197, 86, 602, 834, 428, 692, 724, 824, 992, 7, 11, 67, 259, 13, 69, 133, 265, 193, 385, 22, 70, 26, 522, 82, 322, 578, 770, 44, 396, 52, 84, 660, 164, 196, 56, 536, 296, 776, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_397, vertices_197, vertices_86, vertices_602, vertices_834, vertices_428, vertices_692, vertices_724, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_133, vertices_265, vertices_193, vertices_385, vertices_22, vertices_70, vertices_26, vertices_522, vertices_82, vertices_322, vertices_578, vertices_770, vertices_44, vertices_396, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_397), (false, vertices_197), (true, vertices_82), (true, vertices_578), (true, vertices_84), (true, vertices_660), (true, vertices_164), (true, vertices_536), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_660) then 21 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_704) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 4 5 6 7 8 992 416 1
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_2 3 1 2 6 7 396
cert_row_2 4 1 3 6 8 660
cert_rows_2
cert_pivot 0 5 4 2 1
cert_heightProof 5
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 428
cert_cover_5 3 3 1 2 4 6 44 428 3
cert_coverFacet 4 692
cert_cover_5 4 4 1 3 4 6 52 692 3
cert_coverFacet 5 724
cert_cover_5 5 4 1 3 5 6 84 724 3
cert_coverFacet 6 824
cert_cover_5 6 2 2 3 4 7 56 824 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0408

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0409.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0409

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 653, 197, 897, 342, 282, 684, 244, 632, 856, 992, 7, 11, 67, 259, 13, 69, 133, 521, 193, 385, 641, 769, 22, 70, 26, 266, 274, 322, 44, 652, 52, 84, 164, 196, 56, 600, 280, 552, 776, 112, 336, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_653, vertices_197, vertices_897, vertices_342, vertices_282, vertices_684, vertices_244, vertices_632, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_133, vertices_521, vertices_193, vertices_385, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_652, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_600, vertices_280, vertices_552, vertices_776, vertices_112, vertices_336, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_653), (false, vertices_197), (false, vertices_897), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_600), (true, vertices_280), (true, vertices_552), (true, vertices_112), (true, vertices_336), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_897) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_600) then 21 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_2 3 2 3 5 8 600
cert_row_2 4 1 2 6 8 652
cert_rows_2
cert_pivot 0 7 4 3 1
cert_heightProof 5
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 684
cert_cover_5 2 4 1 2 4 6 44 684 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 52 244 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 600 856 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0409

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0410.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0410

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 341, 793, 206, 650, 898, 684, 244, 568, 880, 992, 7, 11, 67, 259, 21, 69, 25, 777, 273, 321, 14, 70, 138, 522, 194, 386, 642, 770, 44, 140, 52, 84, 164, 196, 56, 536, 552, 648, 112, 560, 336, 784, 224, 864, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_341, vertices_793, vertices_206, vertices_650, vertices_898, vertices_684, vertices_244, vertices_568, vertices_880, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_777, vertices_273, vertices_321, vertices_14, vertices_70, vertices_138, vertices_522, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_536, vertices_552, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_864, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_341), (false, vertices_793), (true, vertices_138), (true, vertices_642), (true, vertices_140), (true, vertices_164), (true, vertices_196), (true, vertices_552), (true, vertices_648), (true, vertices_112), (true, vertices_560), (true, vertices_224), (true, vertices_864), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_864) then 23 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(true, vertices_864), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 7 8 864
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 244
cert_cover_5 4 3 1 3 4 5 52 244 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 112 880 3
cert_coverFacet 7 992
cert_cover_5 7 0 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0410

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0411.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0411

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 341, 233, 625, 782, 454, 650, 898, 796, 696, 848, 992, 7, 11, 67, 21, 69, 41, 201, 49, 81, 97, 14, 70, 262, 138, 522, 194, 386, 642, 770, 28, 780, 276, 324, 56, 536, 168, 648, 560, 336, 592, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_341, vertices_233, vertices_625, vertices_782, vertices_454, vertices_650, vertices_898, vertices_796, vertices_696, vertices_848, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_201, vertices_49, vertices_81, vertices_97, vertices_14, vertices_70, vertices_262, vertices_138, vertices_522, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_780, vertices_276, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_341), (false, vertices_233), (false, vertices_625), (true, vertices_262), (true, vertices_522), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_648), (true, vertices_784), (true, vertices_672), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 14 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_780) then 17 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 2 7 8 780
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 796
cert_cover_5 4 1 1 2 3 7 28 796 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0411

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0412.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0412

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 341, 793, 654, 198, 898, 236, 116, 696, 880, 992, 7, 11, 67, 259, 21, 69, 25, 777, 273, 321, 14, 70, 134, 522, 194, 386, 642, 770, 44, 140, 52, 84, 100, 196, 56, 536, 168, 648, 112, 560, 336, 784, 224, 864, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_341, vertices_793, vertices_654, vertices_198, vertices_898, vertices_236, vertices_116, vertices_696, vertices_880, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_777, vertices_273, vertices_321, vertices_14, vertices_70, vertices_134, vertices_522, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_100, vertices_196, vertices_56, vertices_536, vertices_168, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_864, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_341), (false, vertices_793), (true, vertices_134), (true, vertices_642), (true, vertices_140), (true, vertices_100), (true, vertices_196), (true, vertices_168), (true, vertices_648), (true, vertices_112), (true, vertices_560), (true, vertices_224), (true, vertices_864), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_864) then 23 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(true, vertices_864), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 7 8 864
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 112 880 3
cert_coverFacet 7 992
cert_cover_5 7 0 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0412

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0413.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0413

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 195, 341, 681, 241, 782, 454, 898, 796, 632, 848, 992, 7, 11, 67, 131, 21, 69, 41, 649, 49, 81, 161, 193, 14, 70, 262, 522, 194, 386, 642, 770, 28, 780, 276, 324, 56, 536, 552, 112, 336, 592, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_195, vertices_341, vertices_681, vertices_241, vertices_782, vertices_454, vertices_898, vertices_796, vertices_632, vertices_848, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_41, vertices_649, vertices_49, vertices_81, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_780, vertices_276, vertices_324, vertices_56, vertices_536, vertices_552, vertices_112, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_195), (false, vertices_341), (false, vertices_681), (false, vertices_241), (true, vertices_262), (true, vertices_386), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 13 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 2 7 8 780
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 28 796 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0413

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0414.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0414

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 341, 233, 817, 353, 782, 454, 650, 898, 796, 696, 992, 7, 11, 67, 21, 69, 41, 201, 49, 273, 97, 289, 321, 14, 70, 262, 138, 522, 194, 386, 642, 770, 28, 780, 276, 324, 56, 536, 168, 648, 560, 784, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_341, vertices_233, vertices_817, vertices_353, vertices_782, vertices_454, vertices_650, vertices_898, vertices_796, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_201, vertices_49, vertices_273, vertices_97, vertices_289, vertices_321, vertices_14, vertices_70, vertices_262, vertices_138, vertices_522, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_780, vertices_276, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_341), (false, vertices_233), (false, vertices_817), (false, vertices_353), (true, vertices_262), (true, vertices_522), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 13 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 2 7 8 780
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 796
cert_cover_5 4 1 1 2 3 7 28 796 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0414

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0415.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0415

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 341, 793, 78, 714, 898, 236, 820, 484, 696, 928, 7, 11, 67, 259, 21, 69, 25, 777, 273, 321, 14, 70, 74, 522, 194, 386, 642, 770, 44, 76, 52, 276, 228, 292, 324, 56, 536, 168, 200, 648, 560, 784, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_341, vertices_793, vertices_78, vertices_714, vertices_898, vertices_236, vertices_820, vertices_484, vertices_696, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_777, vertices_273, vertices_321, vertices_14, vertices_70, vertices_74, vertices_522, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_52, vertices_276, vertices_228, vertices_292, vertices_324, vertices_56, vertices_536, vertices_168, vertices_200, vertices_648, vertices_560, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_341), (false, vertices_793), (true, vertices_74), (true, vertices_642), (true, vertices_76), (true, vertices_228), (true, vertices_292), (true, vertices_168), (true, vertices_200), (true, vertices_648), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 20 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_228) then 18 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_2 1 1 4 5 6 228
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 74 714 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 236
cert_cover_5 3 1 1 2 4 5 44 236 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 7 228 484 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0415

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0416.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0416

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 341, 793, 78, 714, 898, 236, 820, 932, 452, 696, 7, 11, 67, 259, 21, 69, 25, 777, 273, 321, 14, 70, 74, 522, 194, 386, 642, 770, 44, 76, 52, 276, 164, 804, 196, 324, 388, 56, 536, 168, 200, 648, 560, 784, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_341, vertices_793, vertices_78, vertices_714, vertices_898, vertices_236, vertices_820, vertices_932, vertices_452, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_777, vertices_273, vertices_321, vertices_14, vertices_70, vertices_74, vertices_522, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_52, vertices_276, vertices_164, vertices_804, vertices_196, vertices_324, vertices_388, vertices_56, vertices_536, vertices_168, vertices_200, vertices_648, vertices_560, vertices_784, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_341), (false, vertices_793), (true, vertices_74), (true, vertices_642), (true, vertices_76), (true, vertices_164), (true, vertices_804), (true, vertices_196), (true, vertices_388), (true, vertices_168), (true, vertices_200), (true, vertices_648), (true, vertices_560), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 20 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_804) then 18 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 74 714 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 932
cert_cover_5 5 0 1 4 6 7 164 932 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 56 696 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0416

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0417.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0417

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 195, 341, 233, 369, 782, 454, 898, 796, 696, 816, 992, 7, 11, 67, 131, 21, 69, 41, 137, 49, 337, 97, 193, 14, 70, 262, 522, 194, 386, 642, 770, 28, 780, 276, 324, 56, 536, 168, 648, 304, 560, 784, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_195, vertices_341, vertices_233, vertices_369, vertices_782, vertices_454, vertices_898, vertices_796, vertices_696, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_337, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_386, vertices_642, vertices_770, vertices_28, vertices_780, vertices_276, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_304, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_195), (false, vertices_341), (false, vertices_233), (false, vertices_369), (true, vertices_262), (true, vertices_386), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_560), (true, vertices_784), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 2 7 8 780
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 28 796 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0417

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0418.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0418

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 205, 905, 342, 538, 786, 684, 244, 568, 880, 992, 7, 11, 67, 259, 13, 69, 137, 777, 193, 385, 22, 70, 26, 522, 274, 530, 322, 770, 44, 140, 52, 84, 164, 196, 56, 536, 552, 648, 112, 560, 336, 784, 224, 864, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_205, vertices_905, vertices_342, vertices_538, vertices_786, vertices_684, vertices_244, vertices_568, vertices_880, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_137, vertices_777, vertices_193, vertices_385, vertices_22, vertices_70, vertices_26, vertices_522, vertices_274, vertices_530, vertices_322, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_536, vertices_552, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_864, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_205), (false, vertices_905), (true, vertices_274), (true, vertices_530), (true, vertices_84), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_224), (true, vertices_864), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_864) then 23 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(true, vertices_864), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_2 1 4 5 7 8 864
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 0 7 2 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 244
cert_cover_5 4 3 1 3 4 5 52 244 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 880
cert_cover_5 6 1 3 4 5 7 112 880 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0418

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0419.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0419

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 205, 905, 86, 538, 850, 684, 372, 484, 568, 944, 7, 11, 67, 259, 13, 69, 137, 777, 193, 385, 22, 70, 26, 522, 82, 530, 322, 770, 44, 140, 52, 84, 356, 164, 196, 56, 536, 552, 648, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_205, vertices_905, vertices_86, vertices_538, vertices_850, vertices_684, vertices_372, vertices_484, vertices_568, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_137, vertices_777, vertices_193, vertices_385, vertices_22, vertices_70, vertices_26, vertices_522, vertices_82, vertices_530, vertices_322, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_536, vertices_552, vertices_648, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_205), (false, vertices_905), (true, vertices_82), (true, vertices_530), (true, vertices_84), (true, vertices_356), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 20 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_356) then 18 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_2 1 1 4 5 7 356
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 5 1 3
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 372
cert_cover_5 4 1 1 3 4 5 52 372 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 6 356 484 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0419

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0420.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0420

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 341, 233, 625, 782, 454, 906, 540, 788, 696, 848, 992, 7, 11, 67, 21, 69, 41, 201, 49, 81, 97, 14, 70, 262, 138, 778, 194, 386, 28, 524, 276, 532, 324, 772, 56, 536, 168, 648, 560, 336, 592, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_341, vertices_233, vertices_625, vertices_782, vertices_454, vertices_906, vertices_540, vertices_788, vertices_696, vertices_848, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_201, vertices_49, vertices_81, vertices_97, vertices_14, vertices_70, vertices_262, vertices_138, vertices_778, vertices_194, vertices_386, vertices_28, vertices_524, vertices_276, vertices_532, vertices_324, vertices_772, vertices_56, vertices_536, vertices_168, vertices_648, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_341), (false, vertices_233), (false, vertices_625), (true, vertices_262), (true, vertices_778), (true, vertices_386), (true, vertices_524), (true, vertices_532), (true, vertices_772), (true, vertices_536), (true, vertices_648), (true, vertices_784), (true, vertices_672), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 13 20 15 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 21 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_625) then 17 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_778) then 19 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
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
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0420

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0421.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0421

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 325, 233, 625, 833, 782, 454, 906, 540, 696, 992, 7, 11, 67, 21, 69, 261, 41, 201, 49, 529, 97, 321, 577, 769, 14, 70, 262, 138, 778, 194, 386, 28, 524, 532, 324, 772, 56, 536, 168, 648, 560, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_325, vertices_233, vertices_625, vertices_833, vertices_782, vertices_454, vertices_906, vertices_540, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_261, vertices_41, vertices_201, vertices_49, vertices_529, vertices_97, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_262, vertices_138, vertices_778, vertices_194, vertices_386, vertices_28, vertices_524, vertices_532, vertices_324, vertices_772, vertices_56, vertices_536, vertices_168, vertices_648, vertices_560, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_325), (false, vertices_233), (false, vertices_625), (false, vertices_833), (true, vertices_262), (true, vertices_778), (true, vertices_386), (true, vertices_524), (true, vertices_536), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 11 18 13 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_789) then 12 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_625) then 15 else
  if p.val = (false, vertices_833) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_778) then 17 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0421

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0422.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0422

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 325, 233, 369, 782, 454, 906, 540, 696, 816, 992, 7, 11, 67, 21, 69, 261, 41, 201, 49, 273, 97, 321, 14, 70, 262, 138, 778, 194, 386, 28, 524, 532, 324, 772, 56, 536, 168, 648, 304, 560, 784, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_325, vertices_233, vertices_369, vertices_782, vertices_454, vertices_906, vertices_540, vertices_696, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_261, vertices_41, vertices_201, vertices_49, vertices_273, vertices_97, vertices_321, vertices_14, vertices_70, vertices_262, vertices_138, vertices_778, vertices_194, vertices_386, vertices_28, vertices_524, vertices_532, vertices_324, vertices_772, vertices_56, vertices_536, vertices_168, vertices_648, vertices_304, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_325), (false, vertices_233), (false, vertices_369), (true, vertices_262), (true, vertices_778), (true, vertices_386), (true, vertices_524), (true, vertices_536), (true, vertices_648), (true, vertices_560), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 19 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 20 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_369) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
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
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0422

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0423.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0423

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 341, 233, 817, 353, 782, 454, 906, 540, 788, 696, 992, 7, 11, 67, 21, 69, 41, 201, 49, 273, 97, 289, 321, 14, 70, 262, 138, 778, 194, 386, 28, 524, 276, 532, 324, 772, 56, 536, 168, 648, 560, 784, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_341, vertices_233, vertices_817, vertices_353, vertices_782, vertices_454, vertices_906, vertices_540, vertices_788, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_201, vertices_49, vertices_273, vertices_97, vertices_289, vertices_321, vertices_14, vertices_70, vertices_262, vertices_138, vertices_778, vertices_194, vertices_386, vertices_28, vertices_524, vertices_276, vertices_532, vertices_324, vertices_772, vertices_56, vertices_536, vertices_168, vertices_648, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_341), (false, vertices_233), (false, vertices_817), (false, vertices_353), (true, vertices_262), (true, vertices_778), (true, vertices_386), (true, vertices_524), (true, vertices_532), (true, vertices_772), (true, vertices_536), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 12 19 14 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 20 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_778) then 18 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
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
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0423

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0960 : Certifies 960 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0394.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0961 : Certifies 961 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0395.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0962 : Certifies 962 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0396.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0963 : Certifies 963 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0397.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0964 : Certifies 964 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0398.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0965 : Certifies 965 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0399.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0966 : Certifies 966 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0400.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0967 : Certifies 967 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0401.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0968 : Certifies 968 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0402.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0969 : Certifies 969 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0403.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0970 : Certifies 970 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0404.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0971 : Certifies 971 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0405.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0972 : Certifies 972 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0406.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0973 : Certifies 973 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0407.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0974 : Certifies 974 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0408.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0975 : Certifies 975 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0409.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0976 : Certifies 976 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0410.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0977 : Certifies 977 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0411.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0978 : Certifies 978 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0412.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0979 : Certifies 979 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0413.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0980 : Certifies 980 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0414.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0981 : Certifies 981 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0415.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0982 : Certifies 982 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0416.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0983 : Certifies 983 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0417.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0984 : Certifies 984 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0418.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0985 : Certifies 985 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0419.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0986 : Certifies 986 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0420.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0987 : Certifies 987 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0421.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0988 : Certifies 988 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0422.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0989 : Certifies 989 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0423.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B032 (j : Fin 30) :
    Certifies (960 + j.val) := by
  fin_cases j
  · exact projection_0960
  · exact projection_0961
  · exact projection_0962
  · exact projection_0963
  · exact projection_0964
  · exact projection_0965
  · exact projection_0966
  · exact projection_0967
  · exact projection_0968
  · exact projection_0969
  · exact projection_0970
  · exact projection_0971
  · exact projection_0972
  · exact projection_0973
  · exact projection_0974
  · exact projection_0975
  · exact projection_0976
  · exact projection_0977
  · exact projection_0978
  · exact projection_0979
  · exact projection_0980
  · exact projection_0981
  · exact projection_0982
  · exact projection_0983
  · exact projection_0984
  · exact projection_0985
  · exact projection_0986
  · exact projection_0987
  · exact projection_0988
  · exact projection_0989

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
