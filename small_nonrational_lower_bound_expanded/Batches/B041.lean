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
/- Source: ProjectionCertificates/R_one_six_0895.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0895

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 169, 737, 334, 962, 348, 696, 408, 880, 912, 7, 11, 131, 53, 69, 41, 137, 97, 161, 193, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 152, 280, 168, 392, 112, 560, 336, 400, 656, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_169, vertices_737, vertices_334, vertices_962, vertices_348, vertices_696, vertices_408, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_152, vertices_280, vertices_168, vertices_392, vertices_112, vertices_560, vertices_336, vertices_400, vertices_656, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_169), (false, vertices_737), (true, vertices_322), (true, vertices_332), (true, vertices_152), (true, vertices_280), (true, vertices_560), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
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
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_400) then 6 else
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
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
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
cert_row_4 2 2 3 4 6 8 696 56 3
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
cert_coverFacet 3 696
cert_cover_5 3 2 2 3 4 6 56 696 3
cert_coverFacet 4 408
cert_cover_2 4 3 2 6 7 152 408 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0895

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0896.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0896

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 169, 737, 334, 962, 348, 696, 792, 904, 880, 7, 11, 131, 53, 69, 41, 137, 97, 161, 193, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 280, 536, 168, 392, 648, 776, 112, 560, 336, 784, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_169, vertices_737, vertices_334, vertices_962, vertices_348, vertices_696, vertices_792, vertices_904, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_536, vertices_168, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_169), (false, vertices_737), (true, vertices_322), (true, vertices_332), (true, vertices_280), (true, vertices_536), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
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
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
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
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
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
cert_row_4 2 2 3 4 6 8 696 56 3
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
cert_coverFacet 3 696
cert_cover_5 3 2 2 3 4 6 56 696 3
cert_coverFacet 4 792
cert_cover_2 4 3 2 7 8 280 792 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0896

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0897.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0897

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 117, 553, 649, 737, 334, 962, 348, 568, 920, 880, 7, 11, 131, 53, 69, 41, 137, 521, 97, 545, 193, 641, 14, 70, 266, 194, 322, 386, 28, 332, 84, 56, 280, 536, 552, 392, 648, 112, 560, 336, 784, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_117, vertices_553, vertices_649, vertices_737, vertices_334, vertices_962, vertices_348, vertices_568, vertices_920, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_137, vertices_521, vertices_97, vertices_545, vertices_193, vertices_641, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_536, vertices_552, vertices_392, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_117), (false, vertices_553), (false, vertices_649), (false, vertices_737), (true, vertices_322), (true, vertices_332), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_395) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_737) then 20 else
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
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
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
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0897

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0898.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0898

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 117, 553, 225, 929, 334, 778, 962, 348, 824, 496, 7, 11, 131, 53, 69, 41, 521, 97, 161, 545, 193, 641, 14, 70, 266, 522, 194, 322, 642, 770, 28, 332, 84, 56, 280, 552, 776, 112, 304, 336, 224, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_117, vertices_553, vertices_225, vertices_929, vertices_334, vertices_778, vertices_962, vertices_348, vertices_824, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_641, vertices_14, vertices_70, vertices_266, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_332, vertices_84, vertices_56, vertices_280, vertices_552, vertices_776, vertices_112, vertices_304, vertices_336, vertices_224, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_117), (false, vertices_553), (false, vertices_225), (false, vertices_929), (true, vertices_266), (true, vertices_322), (true, vertices_770), (true, vertices_332), (true, vertices_280), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_117) then 15 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_332) then 16 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
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
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 348
cert_cover_5 3 0 1 2 3 5 28 348 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0898

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0899.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0899

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 341, 681, 817, 206, 650, 962, 124, 232, 496, 928, 7, 11, 259, 21, 325, 41, 521, 49, 273, 545, 769, 14, 70, 138, 522, 194, 322, 642, 770, 60, 76, 84, 104, 168, 200, 648, 112, 304, 336, 224, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_341, vertices_681, vertices_817, vertices_206, vertices_650, vertices_962, vertices_124, vertices_232, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_325, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_138, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_341), (false, vertices_681), (false, vertices_817), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_76), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_224), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0899

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0900.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0900

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 341, 681, 177, 913, 206, 650, 962, 124, 232, 496, 7, 11, 259, 21, 325, 41, 521, 49, 145, 273, 161, 641, 769, 14, 70, 138, 522, 194, 322, 642, 770, 60, 76, 84, 104, 168, 200, 648, 112, 176, 336, 400, 224, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_341, vertices_681, vertices_177, vertices_913, vertices_206, vertices_650, vertices_962, vertices_124, vertices_232, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_325, vertices_41, vertices_521, vertices_49, vertices_145, vertices_273, vertices_161, vertices_641, vertices_769, vertices_14, vertices_70, vertices_138, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_341), (false, vertices_681), (false, vertices_177), (false, vertices_913), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_76), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
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
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0900

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0901.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0901

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 327, 779, 341, 681, 817, 206, 650, 962, 124, 232, 752, 848, 7, 11, 259, 21, 325, 41, 521, 49, 273, 545, 769, 14, 70, 138, 522, 194, 322, 642, 770, 60, 76, 84, 104, 168, 200, 648, 112, 560, 336, 592, 784, 224, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_341, vertices_681, vertices_817, vertices_206, vertices_650, vertices_962, vertices_124, vertices_232, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_325, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_138, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_104, vertices_168, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_341), (false, vertices_681), (false, vertices_817), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_76), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_592), (true, vertices_224), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_200) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
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
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 232
cert_cover_2 4 4 2 5 6 104 232 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0901

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0904.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0904

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 651, 789, 809, 369, 206, 838, 962, 124, 340, 488, 904, 7, 11, 515, 21, 517, 41, 521, 49, 273, 289, 769, 14, 70, 518, 138, 194, 834, 642, 60, 76, 84, 276, 324, 772, 104, 296, 200, 392, 648, 776, 112, 336, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_651, vertices_789, vertices_809, vertices_369, vertices_206, vertices_838, vertices_962, vertices_124, vertices_340, vertices_488, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_521, vertices_49, vertices_273, vertices_289, vertices_769, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_834, vertices_642, vertices_60, vertices_76, vertices_84, vertices_276, vertices_324, vertices_772, vertices_104, vertices_296, vertices_200, vertices_392, vertices_648, vertices_776, vertices_112, vertices_336, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_651), (false, vertices_789), (false, vertices_809), (false, vertices_369), (true, vertices_70), (true, vertices_194), (true, vertices_834), (true, vertices_76), (true, vertices_84), (true, vertices_324), (true, vertices_104), (true, vertices_200), (true, vertices_392), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_834) then 13 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 5 7 8 834
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 2 5 6 206 14 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0904

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0905.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0905

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 651, 789, 233, 689, 206, 838, 962, 124, 340, 496, 912, 7, 11, 515, 21, 517, 41, 137, 49, 529, 161, 641, 14, 70, 518, 138, 194, 834, 642, 60, 76, 84, 276, 324, 772, 104, 200, 112, 176, 336, 400, 656, 784, 224, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_651, vertices_789, vertices_233, vertices_689, vertices_206, vertices_838, vertices_962, vertices_124, vertices_340, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_641, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_834, vertices_642, vertices_60, vertices_76, vertices_84, vertices_276, vertices_324, vertices_772, vertices_104, vertices_200, vertices_112, vertices_176, vertices_336, vertices_400, vertices_656, vertices_784, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_651), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_70), (true, vertices_194), (true, vertices_834), (true, vertices_76), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_400), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_834) then 13 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_2 0 0 5 7 8 834
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0905

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0906.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0906

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 651, 789, 169, 369, 929, 206, 838, 962, 124, 340, 488, 7, 11, 515, 21, 517, 41, 137, 49, 273, 161, 289, 641, 769, 14, 70, 518, 138, 194, 834, 642, 60, 76, 84, 276, 324, 772, 104, 168, 200, 112, 336, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_651, vertices_789, vertices_169, vertices_369, vertices_929, vertices_206, vertices_838, vertices_962, vertices_124, vertices_340, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_137, vertices_49, vertices_273, vertices_161, vertices_289, vertices_641, vertices_769, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_834, vertices_642, vertices_60, vertices_76, vertices_84, vertices_276, vertices_324, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_336, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_651), (false, vertices_789), (false, vertices_169), (false, vertices_369), (false, vertices_929), (true, vertices_70), (true, vertices_194), (true, vertices_834), (true, vertices_76), (true, vertices_84), (true, vertices_324), (true, vertices_104), (true, vertices_200), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 11 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_369) then 18 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_834) then 12 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 2 5 6 206 14 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 8 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 488
cert_cover_5 5 3 2 4 5 6 104 488 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0906

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0907.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0907

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 519, 651, 789, 233, 305, 929, 206, 838, 962, 124, 340, 496, 7, 11, 515, 21, 517, 41, 137, 49, 273, 161, 289, 641, 769, 14, 70, 518, 138, 194, 834, 642, 60, 76, 84, 276, 324, 772, 104, 200, 112, 304, 336, 224, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_651, vertices_789, vertices_233, vertices_305, vertices_929, vertices_206, vertices_838, vertices_962, vertices_124, vertices_340, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_137, vertices_49, vertices_273, vertices_161, vertices_289, vertices_641, vertices_769, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_834, vertices_642, vertices_60, vertices_76, vertices_84, vertices_276, vertices_324, vertices_772, vertices_104, vertices_200, vertices_112, vertices_304, vertices_336, vertices_224, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_651), (false, vertices_789), (false, vertices_233), (false, vertices_305), (false, vertices_929), (true, vertices_70), (true, vertices_194), (true, vertices_834), (true, vertices_76), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 11 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_233) then 17 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_834) then 12 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_2 0 0 5 7 8 834
cert_row_4 1 0 1 2 5 6 206 14 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 0 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 124
cert_cover_5 3 2 1 2 3 5 60 124 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0907

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0920.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0920

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 267, 661, 297, 817, 961, 206, 458, 124, 212, 872, 752, 7, 11, 259, 21, 133, 41, 265, 49, 529, 289, 385, 641, 769, 14, 134, 202, 266, 386, 60, 76, 84, 148, 196, 104, 296, 328, 112, 560, 208, 656, 608, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_267, vertices_661, vertices_297, vertices_817, vertices_961, vertices_206, vertices_458, vertices_124, vertices_212, vertices_872, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_296, vertices_328, vertices_112, vertices_560, vertices_208, vertices_656, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_267), (false, vertices_661), (false, vertices_297), (false, vertices_817), (false, vertices_961), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_661) then 15 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_202) then 12 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0920

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0921.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0921

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 267, 661, 297, 625, 929, 206, 458, 124, 212, 872, 976, 7, 11, 259, 21, 133, 41, 265, 49, 529, 289, 545, 385, 641, 14, 134, 202, 266, 386, 60, 76, 84, 148, 196, 104, 296, 328, 112, 208, 592, 656, 608, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_267, vertices_661, vertices_297, vertices_625, vertices_929, vertices_206, vertices_458, vertices_124, vertices_212, vertices_872, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_545, vertices_385, vertices_641, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_296, vertices_328, vertices_112, vertices_208, vertices_592, vertices_656, vertices_608, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_267), (false, vertices_661), (false, vertices_297), (false, vertices_625), (false, vertices_929), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_328), (true, vertices_208), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_661) then 15 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_625) then 18 else
  if p.val = (false, vertices_929) then 20 else
  if p.val = (true, vertices_202) then 12 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0921

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0922.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0922

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 267, 149, 809, 689, 961, 206, 458, 124, 724, 360, 880, 7, 11, 259, 21, 133, 41, 265, 49, 145, 545, 385, 641, 769, 14, 134, 202, 266, 386, 60, 76, 84, 148, 196, 104, 296, 328, 112, 560, 592, 656, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_267, vertices_149, vertices_809, vertices_689, vertices_961, vertices_206, vertices_458, vertices_124, vertices_724, vertices_360, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_265, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_296, vertices_328, vertices_112, vertices_560, vertices_592, vertices_656, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_267), (false, vertices_149), (false, vertices_809), (false, vertices_689), (false, vertices_961), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_202) then 12 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_352) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0922

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0923.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0923

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 267, 149, 809, 625, 913, 206, 458, 124, 724, 360, 992, 7, 11, 259, 21, 133, 41, 265, 49, 145, 529, 545, 385, 769, 14, 134, 202, 266, 386, 60, 76, 84, 148, 196, 104, 296, 328, 112, 592, 656, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_267, vertices_149, vertices_809, vertices_625, vertices_913, vertices_206, vertices_458, vertices_124, vertices_724, vertices_360, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_265, vertices_49, vertices_145, vertices_529, vertices_545, vertices_385, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_296, vertices_328, vertices_112, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_267), (false, vertices_149), (false, vertices_809), (false, vertices_625), (false, vertices_913), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_328), (true, vertices_352), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_625) then 18 else
  if p.val = (false, vertices_913) then 19 else
  if p.val = (true, vertices_202) then 12 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 1 3 5 6 8 724 84 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 84 724 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0923

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0924.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0924

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 721, 897, 270, 458, 812, 628, 360, 992, 7, 11, 131, 21, 261, 57, 73, 81, 529, 193, 385, 641, 769, 14, 262, 202, 266, 386, 44, 268, 52, 532, 548, 772, 104, 296, 328, 112, 592, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_721, vertices_897, vertices_270, vertices_458, vertices_812, vertices_628, vertices_360, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_202, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_296, vertices_328, vertices_112, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_721), (false, vertices_897), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 0 2 5 6 202
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0924

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0925.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0925

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 899, 789, 121, 721, 270, 458, 812, 628, 360, 992, 7, 11, 131, 259, 21, 261, 57, 73, 81, 529, 193, 641, 769, 14, 262, 202, 266, 386, 44, 268, 52, 532, 548, 772, 104, 296, 328, 112, 592, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_899, vertices_789, vertices_121, vertices_721, vertices_270, vertices_458, vertices_812, vertices_628, vertices_360, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_641, vertices_769, vertices_14, vertices_262, vertices_202, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_296, vertices_328, vertices_112, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_899), (false, vertices_789), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_899) then 12 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 0 2 5 6 202
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0925

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0926.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0926

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 149, 553, 625, 913, 206, 458, 124, 724, 872, 960, 7, 11, 259, 21, 133, 41, 521, 49, 145, 529, 545, 385, 769, 14, 134, 202, 266, 386, 60, 76, 84, 148, 196, 104, 552, 328, 776, 112, 592, 656, 608, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_149, vertices_553, vertices_625, vertices_913, vertices_206, vertices_458, vertices_124, vertices_724, vertices_872, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_385, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_592, vertices_656, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_149), (false, vertices_553), (false, vertices_625), (false, vertices_913), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_328), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 10 19 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_625) then 14 else
  if p.val = (false, vertices_913) then 15 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 5 60 124 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 872
cert_cover_5 4 3 2 4 5 7 104 872 3
cert_coverFacet 5 960
cert_cover_2 5 6 5 7 8 448 960 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0926

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0927.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0927

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 213, 553, 561, 913, 206, 458, 124, 872, 752, 960, 7, 11, 259, 21, 133, 41, 521, 49, 145, 529, 545, 385, 769, 14, 134, 202, 266, 386, 60, 76, 84, 196, 104, 552, 328, 776, 112, 560, 208, 656, 608, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_213, vertices_553, vertices_561, vertices_913, vertices_206, vertices_458, vertices_124, vertices_872, vertices_752, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_385, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_213), (false, vertices_553), (false, vertices_561), (false, vertices_913), (true, vertices_202), (true, vertices_76), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 10 19 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_213) then 12 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (false, vertices_913) then 15 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 872
cert_cover_5 3 2 2 4 5 7 104 872 3
cert_coverFacet 4 752
cert_cover_5 4 3 3 4 5 6 112 752 3
cert_coverFacet 5 960
cert_cover_2 5 6 5 7 8 448 960 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0927

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0928.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0928

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 661, 553, 561, 961, 206, 458, 124, 212, 872, 752, 7, 11, 259, 21, 133, 41, 521, 49, 529, 545, 385, 641, 769, 14, 134, 202, 266, 386, 60, 76, 84, 148, 196, 104, 552, 328, 776, 112, 560, 208, 656, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_661, vertices_553, vertices_561, vertices_961, vertices_206, vertices_458, vertices_124, vertices_212, vertices_872, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_529, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_661), (false, vertices_553), (false, vertices_561), (false, vertices_961), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 10 18 13 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_661) then 12 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_202) then 17 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
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
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 752
cert_cover_5 5 3 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0928

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0929.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0929

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 149, 553, 689, 961, 206, 458, 124, 724, 872, 624, 7, 11, 259, 21, 133, 41, 521, 49, 145, 545, 385, 641, 769, 14, 134, 202, 266, 386, 60, 76, 84, 148, 196, 104, 552, 328, 776, 112, 560, 592, 656, 608, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_149, vertices_553, vertices_689, vertices_961, vertices_206, vertices_458, vertices_124, vertices_724, vertices_872, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_560, vertices_592, vertices_656, vertices_608, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_149), (false, vertices_553), (false, vertices_689), (false, vertices_961), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 10 18 12 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_689) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_202) then 17 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
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
cert_row_2 0 0 2 5 6 202
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_2 2 1 2 3 4 60
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 5 60 124 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 872
cert_cover_5 4 3 2 4 5 7 104 872 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0929

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0930.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0930

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 213, 553, 689, 897, 206, 458, 124, 872, 624, 976, 7, 11, 259, 21, 133, 41, 521, 49, 145, 545, 385, 641, 769, 14, 134, 202, 266, 386, 60, 76, 84, 196, 104, 552, 328, 776, 112, 560, 208, 592, 656, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_213, vertices_553, vertices_689, vertices_897, vertices_206, vertices_458, vertices_124, vertices_872, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_213), (false, vertices_553), (false, vertices_689), (false, vertices_897), (true, vertices_202), (true, vertices_76), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 10 19 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_213) then 12 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_689) then 15 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 872
cert_cover_5 3 2 2 4 5 7 104 872 3
cert_coverFacet 4 624
cert_cover_2 4 4 3 5 8 112 624 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0930

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0931.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0931

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 661, 553, 625, 897, 206, 458, 124, 212, 872, 976, 7, 11, 259, 21, 133, 41, 521, 49, 529, 545, 385, 641, 769, 14, 134, 202, 266, 386, 60, 76, 84, 148, 196, 104, 552, 328, 776, 112, 208, 592, 656, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_661, vertices_553, vertices_625, vertices_897, vertices_206, vertices_458, vertices_124, vertices_212, vertices_872, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_529, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_208, vertices_592, vertices_656, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_661), (false, vertices_553), (false, vertices_625), (false, vertices_897), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_328), (true, vertices_208), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 10 19 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_661) then 12 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_625) then 15 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0931

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0932.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0932

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 213, 553, 689, 897, 206, 458, 124, 872, 496, 928, 7, 11, 259, 21, 133, 41, 521, 49, 145, 545, 385, 641, 769, 14, 134, 202, 266, 386, 60, 76, 84, 196, 104, 552, 328, 776, 112, 176, 208, 352, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_213, vertices_553, vertices_689, vertices_897, vertices_206, vertices_458, vertices_124, vertices_872, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_176, vertices_208, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_213), (false, vertices_553), (false, vertices_689), (false, vertices_897), (true, vertices_202), (true, vertices_76), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_352), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 10 19 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_213) then 12 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_689) then 15 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 872
cert_cover_5 3 2 2 4 5 7 104 872 3
cert_coverFacet 4 496
cert_cover_5 4 3 3 4 5 6 112 496 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0932

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0933.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0933

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 213, 553, 561, 913, 206, 458, 124, 872, 496, 816, 7, 11, 259, 21, 133, 41, 521, 49, 145, 529, 545, 385, 769, 14, 134, 202, 266, 386, 60, 76, 84, 196, 104, 552, 328, 776, 112, 304, 560, 208, 400, 784, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_213, vertices_553, vertices_561, vertices_913, vertices_206, vertices_458, vertices_124, vertices_872, vertices_496, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_385, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_784, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_213), (false, vertices_553), (false, vertices_561), (false, vertices_913), (true, vertices_202), (true, vertices_76), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_304), (true, vertices_352), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 10 19 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_213) then 12 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_561) then 1 else
  if p.val = (false, vertices_913) then 15 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 872
cert_cover_5 3 2 2 4 5 7 104 872 3
cert_coverFacet 4 496
cert_cover_5 4 3 3 4 5 6 112 496 3
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0933

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0934.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0934

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 779, 789, 553, 625, 206, 458, 124, 212, 404, 872, 976, 7, 11, 259, 21, 261, 41, 521, 49, 529, 545, 769, 14, 134, 202, 266, 386, 60, 76, 84, 148, 276, 196, 388, 104, 552, 328, 776, 112, 208, 592, 400, 784, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_789, vertices_553, vertices_625, vertices_206, vertices_458, vertices_124, vertices_212, vertices_404, vertices_872, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_41, vertices_521, vertices_49, vertices_529, vertices_545, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_208, vertices_592, vertices_400, vertices_784, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_789), (false, vertices_553), (false, vertices_625), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_104), (true, vertices_328), (true, vertices_208), (true, vertices_400), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 11 20 14 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_789) then 13 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 124
cert_cover_5 2 1 1 2 3 5 60 124 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0934

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0935.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0935

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 721, 897, 782, 458, 556, 628, 872, 960, 7, 11, 131, 21, 261, 57, 73, 81, 529, 193, 385, 641, 769, 14, 262, 202, 266, 386, 44, 524, 52, 532, 548, 772, 104, 552, 328, 776, 112, 592, 608, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_721, vertices_897, vertices_782, vertices_458, vertices_556, vertices_628, vertices_872, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_202, vertices_266, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_592, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_721), (false, vertices_897), (true, vertices_266), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_608), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 872
cert_cover_5 4 3 2 4 5 7 104 872 3
cert_coverFacet 5 960
cert_cover_2 5 6 5 7 8 448 960 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0935

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0936.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0936

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 213, 553, 689, 206, 458, 898, 124, 872, 624, 976, 7, 11, 515, 21, 133, 41, 521, 49, 145, 545, 641, 14, 134, 202, 266, 386, 642, 770, 60, 76, 84, 196, 104, 552, 328, 776, 112, 560, 208, 592, 656, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_213, vertices_553, vertices_689, vertices_206, vertices_458, vertices_898, vertices_124, vertices_872, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_641, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_213), (false, vertices_553), (false, vertices_689), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 11 20 14 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_213) then 13 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_689) then 16 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0936

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0937.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0937

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 779, 213, 553, 689, 206, 458, 898, 124, 872, 496, 928, 7, 11, 515, 21, 133, 41, 521, 49, 145, 545, 641, 14, 134, 202, 266, 386, 642, 770, 60, 76, 84, 196, 104, 552, 328, 776, 112, 176, 208, 352, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_213, vertices_553, vertices_689, vertices_206, vertices_458, vertices_898, vertices_124, vertices_872, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_641, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_176, vertices_208, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_213), (false, vertices_553), (false, vertices_689), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_104), (true, vertices_328), (true, vertices_112), (true, vertices_352), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 11 20 14 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 12 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_213) then 13 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_689) then 16 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 1 2 3 4 60
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 124
cert_cover_5 3 1 1 2 3 5 60 124 3
cert_coverFacet 4 872
cert_cover_5 4 2 2 4 5 7 104 872 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0937

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0938.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0938

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 451, 117, 553, 865, 526, 902, 668, 212, 632, 976, 7, 11, 195, 259, 53, 69, 41, 521, 97, 545, 321, 769, 14, 134, 518, 522, 386, 770, 28, 524, 84, 148, 196, 644, 56, 536, 552, 112, 208, 592, 656, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_553, vertices_865, vertices_526, vertices_902, vertices_668, vertices_212, vertices_632, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_545, vertices_321, vertices_769, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_148, vertices_196, vertices_644, vertices_56, vertices_536, vertices_552, vertices_112, vertices_208, vertices_592, vertices_656, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_553), (false, vertices_865), (true, vertices_518), (true, vertices_524), (true, vertices_148), (true, vertices_644), (true, vertices_536), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 10 12 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_117) then 11 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_865) then 20 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 134 3
cert_row_4 1 1 2 3 6 8 668 28 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 134 902 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0938

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1230 : Certifies 1230 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0895.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1231 : Certifies 1231 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0896.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1232 : Certifies 1232 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0897.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1233 : Certifies 1233 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0898.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1234 : Certifies 1234 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0899.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1235 : Certifies 1235 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0900.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1236 : Certifies 1236 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0901.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1237 : Certifies 1237 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0904.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1238 : Certifies 1238 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0905.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1239 : Certifies 1239 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0906.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1240 : Certifies 1240 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0907.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1241 : Certifies 1241 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0920.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1242 : Certifies 1242 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0921.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1243 : Certifies 1243 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0922.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1244 : Certifies 1244 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0923.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1245 : Certifies 1245 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0924.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1246 : Certifies 1246 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0925.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1247 : Certifies 1247 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0926.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1248 : Certifies 1248 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0927.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1249 : Certifies 1249 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0928.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1250 : Certifies 1250 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0929.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1251 : Certifies 1251 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0930.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1252 : Certifies 1252 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0931.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1253 : Certifies 1253 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0932.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1254 : Certifies 1254 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0933.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1255 : Certifies 1255 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0934.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1256 : Certifies 1256 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0935.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1257 : Certifies 1257 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0936.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1258 : Certifies 1258 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0937.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1259 : Certifies 1259 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0938.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B041 (j : Fin 30) :
    Certifies (1230 + j.val) := by
  fin_cases j
  · exact projection_1230
  · exact projection_1231
  · exact projection_1232
  · exact projection_1233
  · exact projection_1234
  · exact projection_1235
  · exact projection_1236
  · exact projection_1237
  · exact projection_1238
  · exact projection_1239
  · exact projection_1240
  · exact projection_1241
  · exact projection_1242
  · exact projection_1243
  · exact projection_1244
  · exact projection_1245
  · exact projection_1246
  · exact projection_1247
  · exact projection_1248
  · exact projection_1249
  · exact projection_1250
  · exact projection_1251
  · exact projection_1252
  · exact projection_1253
  · exact projection_1254
  · exact projection_1255
  · exact projection_1256
  · exact projection_1257
  · exact projection_1258
  · exact projection_1259

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
